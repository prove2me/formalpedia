-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3658
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:18:20.757862+00:00
-- url     : https://prove2.me/submissions/37386437-d4db-4983-9c34-0d7122ad7221

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 657733812 ≤ n < 657913669 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 657735062 1250 657733812 657733819
    0x21230130311010513080601090b10020615040204090c08150f0f040207141002030601080105010807080a05041103010c02030d14010f090b03101d0d0503090307060b0f0a0605070302120702 82
    0x1c200040090382c02e40e04081c03040c5002410242e41d904120104e40c17807504400b010360040c400501407a4010304c03500d010340c002242c80005000b028400a500c03458040c10f004003100c02c004c12404540c80d9a01103400500f20350604004020b86000020311034a01074405101c2c2c0b411402c24801e00d880c05040014a80c40024002c0c1c010342002010003000b5440710804451103150003107402504007041c0414031120b01110f8025a0342d00d044400104090016000b0a06108005040c0700301140d2011000b0783c40b04074131000062070745407401d00c0800310000d00307822540340d07080c001c840c940d560f4040064220f0402d9150700340608a2603204103c1e40010900903400c1e11a26414200540801d5400c00460140040c0079141d07080100203800d01500d08020022206910081b600c0241d51410010551008814a8000d05505101200913241c1c0f06550300509241d071111580403c903550b4a900301411400100990030b410740c0e8240c00f030403681021509034054040c401c0300700302c01c03189541212981a4004e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 657736312 1250 657735062 657735097
    0x109081005060a0b0310140613061d03070602030c010509010b0d02060f090a030b2202100f031e0c021204030c03062309070513180201030504021230 65
    0x80510001c04004004940c0500304160001e100c50748400114012004012459000c41c02c1407020518102841a240d000e91010002c925200084011100603118180350540382d500c1d0811424403c0d8281c070081c11b5250043c0b2100144041e0008000c14655184000034425603071003070031060803100074210050704042013040142c01807a20b0f4000742406086404054108036a070310209200740c000d60801c84001040405100d82189480d1030900e84000b0201e0800d4102c0040d8080340440c3c80c4001e007400ad2110200240c8500c500a0f000070000c1c074201010b0b04050b0383d100821801400d880240c0782d016004501c1030603646005281182c00b660b800001041900340303169104402405803c000d40b0b90410f0011075903070352030201851b050042c1ea402c4018003038242020204801030340d464030300c01840d62510380c440d418070b80e943c08001d004a03024207000071207541d54004503541c0c1c9400201c00310706000742c2030140e003500c100080c00c440d101600403440322000304c80c1011f80c2462260340142948040203 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 657737562 1250 657736312 657736333
    0x10501020c180f1e0703200711061602040e0a03080702070e072a05070f050d3507210c03051209010b12060603150408071103011103070f0905010908 65
    0x303107442c3c0c1c1d040f0b6114810703441c0c05513451958003040001501d01e800040d44800035000c001220304a008080c0000c03c02c502d01d840415510900391140842c07405009032001b06d0309940440802c0e95a10b600d03a000317001400320b004021211a20754206200c201c001c21841c1c070100300d0f02d920024109043d180100325018040d110360806070784400c0882100d1043c041ba23000c005080c9903103400d49800c098860303002001101d00b07014840310743d426543c00941c000e00e0080b4845005c140c420344241c0680806103211a050142007040d01e007090201c0300b140402000014003031b010003901c181d03030381d481c40d0030503104100d83d0400f0141241d0b140308104000d40014403d10220b603150110300d0406401c801a240000380003403540b000b080c030310395001c01d502d41c0c1c40c1c1084081151504050107965500810354198103044d14040c0c1e03036512503001b420300c0a0696280740358240c419417025400740f01440711002c4c0c00c1d603c0c1d1a0064000340ba14050340c0b1407000244031408009240d501400d00981a60b0465000e001c80c03104 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 657738812 1250 657737562 657737581
    0x3060112081b0f010f0e0a170c03120f0705070b0a1802030727020901020d050a05040b0d050a0b01020a0c0603110d022a0c0f0f04020d14010501020c18 66
    0x15240644080d80304026500400d24070358a9030044007114005406090b941c103c9a40c04c40c0c0190910343d443c0e40c14605100b40c91140420404429a40125290762000301112843c10314000e03009103054074480000e445044105614000c0d2060186480c1804c0700c0c0c1d06c0480403104c3e4007910000804501c101c3c40420b56803403c80c0c0218030742003030101003441e00d80c4031900042d14012280d44006000400010b010a07403200c0f245112140c6048080254944100340d00000c0d40d0325240000360341000b00205143d40000d120310f0841e4000c104440c2c0c0961591901c61a40009080503240c0b09169481c0c02d000300b200d9400418114041c541285c04452514a8140154040c0014001800c00030004001500d48210b040c8041c01c0e40e0200c0b008807031041c900ca02c12110030081c40b01d4007000680c0c0f004501a0341d960b10a03401c0c51006409403969400441d0800115002e400b50b8808860441d041c1003168046016110740035049550990840f1900202c3c0c80c1031001c0c12001c4030803140d00c211840e00003a030190 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 657740062 1250 657738812 657738839
    0x100801060b0403110f03060c19020109050309060f1204050d120903210207020402031e0105030601150302090406090e01051b090310020a140a02060403020c04020f09040903030f0903020703140a02030601 88
    0x66000d80498000511131000a081c8902100c00c1c1307020240100d0050010708409c01c8a50511010380001c00815049446503a038030b0044078071030751041e4800a4041c00619190b0151400142c4d11340c00165141420304c1c2880c1c542c1010854600040c0540c00400442a0540604840d4030340503103590010481d41080d83c500f000d0322060000903542c0030000c3c9030068131340c0e2004610410300700501048c0100309007544007141806910a40c4a40d201e0001449031000b03103001440b60b003945050041c0d4034030b0300c0340c081806410964850103000c0d2410744410b030340c080190050382c03207210104505504211181d030350041a0180310a080d07015845681d000c0752540542d801411491002d00306100000004100d10303036698030074107505006810420038801015010407848148120403101942000360004030000c56005418004d4440ca031903802030003c1c54000d60281415081e03043d000d2012071100c0c1406503440c2c2c40c2e0311007218541008200c0a06c809008140b41e05035aa0040180919034a0015400b0810 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 657741312 1250 657740062 657740093
    0x1506150c021207091b030207050d0e030c10230a0903030309050a020a0b070c240f090b030109020a110a05120d02130e15040608210f030c03100801060b0403 68
    0x142e2159a8101c1200400c1007400070114008007103005500004088003080300015a90145401400408000354001c02c54180590503858198a020308900000b807a101d19100d000350810031800d003807400d8592103e00115045134011042e4410100c41d00e81842e14415584c0b020005a802601480000d200780c000800307086c040e40031120004d000750001030504031940d02030f03e1980300006100d810009002e40000080900c8802e043e00c4030044400d1002504840880700300700070000224040340c41c050140c0c0f10140800b005501e4503507845d080c6040003907114103803a1001c2105a0400c86030100c000132084882540b202c0900403c404240b20701c41e054006a401400150b0203000050012070109610f40041500340101c040c20f0411038040c41e43c4d0b400c1903c40c81d001e241459010300180b01c0014951140c60150903101c11100801c0c50031107514082c150080030310481c0007090050860aa90245001d2880da40c0008d000a50300c2200324200d0780d46201c0d0100d003403030034081007001c1180b011803821071 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 657742562 1250 657741312 657741319
    0x207060c05030408030a03020912060126101514240c070b0c150705090a0302150f03040b040308010e07020d03050601030605031606090f08070e0702030717071506150c02 74
    0x5044d00c42d440103040d40c0000301c2c1040041d5011894020307034038160351500301e500101c0000d4a401e50401681d21b14070045d400a59800d00035045030515481000c1011811001403c2410082105c00380020b1880801f9031240041c5103800118214041c40c00300c0c0d440718115540b40d1044032240031603e44000b160862608180350f8019510000307888000034005241001a80c00034011868004900b02d42d411409405501009004e1041503c1603d55400040582e60100c0303003001c03202e4901c0b610080c68030a55121100440c00802030100304a40911098081c5200780c5880185a80f0340c144081030071821070790903006a1143ea40d9040ea0381c0a54481508050189404112203132a203001c05e01e012040071038485010f021030001c1200b1030303200c1e24800140484409602c555440c0c81134040e9200114018207814034204404240e02a008108031000d103503002c0c40d01102c148509140040a030000b0345c05694044c40c24000c100e10140520840c800d42d100109a40f082c0c00440004a51520400303904903003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 657743812 1250 657742562 657742567
    0x816060f0c0323070c0b091c0816081902040305032a070e070513031b0816300b0a0f060e18010e0106120204060b0f030c0d0b1008071e0207060c0503 65
    0x206d0354501c549407049402e440201380e003880480d0120000c4690038814401c00100405011100c445440d92910301022850040d105071192500c6030703010315041c10018400b61000600004000001c405041c500000d41c0804c10507198440c0d88641501e0b0101e140c030303e541c0003e841031107401030050000b81c00580c989001070900122816280554109030401e523050700000361960462007a0000c030f81c01820420015226088070a600c01c0c0d44030840340100030440510220310800c0480c0c40000d0500b843c1d4180c0116410340250425000030181540c64541c241d013081e030444102e0300d590140c0c030100c508465503000c0030340da08044490001c03012460104107549a507001521000c007401b0361000707410000442c1d04255494810001150841c0d40045001942400188060400035080d41d0341300c0040c00b03076907a86e07c0c40c401031030703000b044c40c146102c0c3c3c01500b82d03001942503540001c100e032282c2420b84440e050381100f00501d100f00d8038100003880060f8444801400b0691003015a411590300c91400c990 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 657745062 1250 657743812 657743837
    0x2a030304110d060f051302030f0d0f0e1504061806080f070807110609010506030c09150d05031309020a1101200c07030c0b070309061112070816060f0c032307 69
    0x100745c03032054500301002d01031040640b080d8903091003250a4449075600600100b10ba41c40050100401d4194510a020782c1c07981c023000390b4880018a043e40608801010350f500e85031440a071021040721103035074211414003004500503000f014010300580c184081b4150300d07a10344100310345280006084200b017010b05261050101c40401c1b080c3c0c021200400003044c580ba0030403d051a100c800e00c03038144600e805c0c000340b01024040b4400284c1000d0143e0701c50342d5045103800c1043c61840303640c1c022240c00f51010030008a07810507078040c001c3d00010b81e590741e8003c40c0c040c110380d09882c810604501600094040e1100141a400017888048c1100f81030301d01081e40c82e103400302c4885803680189205600041c0c2c1c00200b6900c18488009000c450070005410303a04110025aa00c401c00741c0c2c07080310700000a150090042000940d5806440728a10041c0d5019615140300680b0a1007000c0c1c0c0018103000105144d6402401036100c0c1080c10a000305002c03100c14628410f029001c1d0020090099071600701 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 657746312 1250 657745062 657745091
    0xc0e0402030f070219030804060c05090303070c06031a0f0f1906020a05150f070c0204110d0914010c1b1109011e0603051506070c0801022a030304110d06 67
    0x452040c0940c1494a202c2c0c9450308010b401d010b807401e0404400103007486204006030f00010003d800c2a0001c0b400038001c142d402095400d480740c3e0745210f44c180320108268003049030f106403003015680355640a10a90780a18048480100c0510005a1006440000c05550300341180000300b00c00e00140222000c15903901c86181c0741e6500d03041800141c10444c03940e030601008000c44840341d280c400d29103400e8501005d0075484104040c000404018541c5035084c190346d01d540100c035041c9458000c07141d861a6422841005105030107040300d070b654480c102102e250406124103e2981200e4807010b024040e030f071000b225442440c0008a40d00403020308903030140e80310103203c6406002c0b48140c0388030641d10300c1010501c04d2199800281054101410032440910072888406a103030305942441e2100702d40d2070540100141900807104c958800324005141c0783c0c51450580c1c0101c9150700c03558907808100b82c01912071004941c00f800240140f0902c078128148071001c20095401403100055014a80034413 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 657747562 1250 657746312 657746317
    0x2130c030b0a0b1e07110d050a150605120f0d12060b0307081905011202040c120e1f02040807120f0c0f092708030907030807060203010e060a0602100c0e0402 69
    0x1070070035024082401c1101d03810700f0910307508454130006080c0c20302010b80d899021082c4c001d44060701654410002d407080017420401a10a0795000340994003000040002c0d00c003d03ea6485824400d01003420002c0c4520000300d0500c1d85020624060f0401c008944030940300c04000d89816485a6070741d0f1f2000581145a5001d503002d140c041e51071030b8031703400d14400301501d00b001d94150b030305410725140040200c414101410301c85c441d07040d980400c0700c1120605c01d54008100c020852a658148a206030100c0c102040e19812000e400c185002c441003150008412401513006444269000c48000d0050003040c4800f1340703410b881446039070000003203a0f49880c40c00c0c01c5903104141c00109040148074450150188200207820b4908400c02d02c031172001032100109081c0000b900040300007011030620142408818003440e041101c00f503944000b4a080b9000f58424071408800010781000f086161900203181c1d01250141d900800046016295039002842d20814030300038000c1e8901083d0711034030369002 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 657748812 1250 657747562 657747569
    0x30c010f06050f1206060d0809180103062403080702120d020a0c1706040201030e0c10080f06040603050730050c030c06040617060406090203040c1d0402130c030b0a 72
    0x1012034441d1910043c015850090700805100d140b20b4501640901000900c540d40403000f1140d028410b1024101426144509803d5503000360321080c00510182c000c2068078103ca10420040210040b18103214426030b04102d00104178210250b800c01c082071982c0e0140100c41e0000740850424071000d20318520308142d005000015802404261050190440c07140740240b604250340c821003000407198680b104001000241072590320801c8248042e03040044910b20070300034001c40080003644c0005004060100c40c2200b01c08504c0c8001495401c01c0d01412041302c2c1c3c44002010360394180b100070b810902031804c500884142001c00002000c0704100040f8840f03001d40081c01c1000e44a01c24181051004a0b1302c1d07004820030403081003016484914804040704070940e0a0040e00c8a030002005448582d0014500030300200c14001840030341d40e00c040440d01d100e521a0149105180c104400c0101102c01a6002030321442c512810a440e0f0002c091900c800e1600107850100e0b04000380514030341340c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 657750062 1250 657748812 657748841
    0xc0d09081216080f040305090d1b0906030611091008090109060516030f0b0307140301140406140106090501080c03061f02060709050f06250f0f030e0904021809030c01 73
    0x3120b003070348640010000b81c025800c1c90b00300034a803400b6240074011340f0421007054003a103500b07500c0d042405034503000e80c1100c40980d1340301e01005681d052a0b901409040c00700364ae0203450540c034001002000c1c1e080740c42d04100545a90a80900c0c0e00042c0c90181008041c08015500c0d011000000740003481024800e102046107880e400f01c41c568010308503060400c1c440303c2645015008181c0d5600065964100c13107861044445c041980001300e80540212a10301d903a075401902030208220058110702d020b440c1242c0300900580c2d8400c0c04840708000d03446030a010460020128002c01151001107600c4200941035142d020000c4104c07880c50400c1c1c0d01d24000503000742007440381f140d40c07148030607009080032103024402900c04030002c8d403544140708901d00000d00f40414041c0014885c0180043c0c03682002143d20810200c0c201124007094480c030442c0080c0c000200600c10b85050386586008a0f0090a0124026000d2003c000f6000c4081c044c4e10480c482400f92a038100400d004d044111a98030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 657751312 1250 657750062 657750091
    0x50f0a15020d0e040b0d0b0709031e1208010b040506030a02040e071e230307020708030711100912020f01091518060915030c050d0e0c03060c030c0d090812 68
    0x8480c000c10f160240529540300760308004a0b031301e103595403245040c0d500343c10203074002054882d608281e071250f540e903100400c0301021221104080c9005441291014000c0b0590755191300c240f102155414401d009140c1802c5080c8418001c1c7d041a801442d40000280c0006207450744035240118500021100b04e07000480c00507009070b0924103008c440281030312504001485019502618003c03000c03030440b5020300740d00403001441c8180708105c61001001110152642d441240c200b20f401c3e0454040524050300d5500f050b085900c0c486c024005c01c0702c1e00f903049010703042c0490342040700311180c10503441c0c1000341c000303004a0403041900d0700c0000300c6442e49859501a0403040600030000c001d134011428042035100412031805107000744400d0342c60a180009215100e4101510903000d10950a91080e10b0f02040000143e800542c400c4400b5040b170450381996907041c824185440203d80744403540f01c2c24001c100040c0425041442d04901c0354003094208640128503450442c01110301d00400482e0b03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 657752562 1250 657751312 657751333
    0x30901090b0f0a0b03060c04090509070f0609090608060f06010521150910030809012007060c231b01170a09021f080114030c100807020d0203070c050f0a1502 69
    0x79845800704404c000e07000340099142403c4500b840f070045103e05031820f0f48840005102000902490700a41125504d52f000d641c0c980c00e0003003024016014034055903207000c201045500300040d0040c030030b402420025071155683c00c01102d140e04144a14000401800d01c010100d410304a8883d1080c1d040c00481c10154000b42e0800150034409810b05e078502d502d61134144041040714080741c84c00c1c8000c3c200406032840300c0400480b108242d0411140d076008102012400560080c1c040c1040342c0203c8500f1700d01700b080f01001100e52000e920b0320781d55900c0040c940c2020352940000b6041a4414144200c000c2070000708134503070344812510001c0303080c5d968010300d0841c50010108019a0040c00005805a041d4007001c0e005c15018000d8807074060b400812200580c2c2d08002101c0200c40150020006401b01d640260982c001a900d46000d1b020b0403016180e003620010689982e2a0060500c031407040c9410184807030840100c45180e0807408820703020803103600805100a07208aa0f80c0242580d851 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 657753812 1250 657752562 657752581
    0x1b07050f0d090e01180b030a0b01140f032e0b040f23040b0a1a04020c060114031f0e0304031707020a0614072307080a26030c030901090b0f 61
    0x368000000c41000c40f001484550b1481070001c0c3c588604420010305112040002481e00101c1b010061818a95100100743d285c034080f6800242d45040e101240c104880c04e04254540c0f0301046840b0314212440d803140022104c4007280d2101c07410b403100000e0700b240500003003401d44012080c0c0c0c0c3c1e410354440b030716030041400c134405c00140c54803500001d4280d41010b035905c80710104060500f00d540c5480c0e2100003210f41110f0310340c1c0c0d0111002003045594508074440d544c0c03155000d1042403101541000711010324140820591705005c000664100350300d00120120006107018144038419120038400880003a0412084248108090304901c0e110000f901c1000044c186940042c020082907000c0b503201200202e0075a014180e024011a03c40c035042c8114241164080601d00300611070b11400280c01a80800e071004014018170080100807645030082e031942c1c400c14010740b00c000f0104001051088004040e640140100001080a0344103031142d620480050751140801066942031181c0700c074 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 657755062 1250 657753812 657753827
    0xa08190e060412210b1f1107080d02100e0703020a060207080d0504060c030302090d0818010206180304150c05030403120818030f130504020a0302070212030309061b07050f0d 76
    0x4409103021244101485440e142c90b010900c5004c100b04d0311482d0095069660003c4a080c0c60140c01070707504940d0360b40000400180b06015440c56500803848007148500e00810300203d0302040350004d20b21241c090180708001c0000303442d829100d0140610110040e507030100340c0313802070103258001c1c003450781032400580c24020318103004028840c08005c03c105560f08190408a60380d0941001a21003a10703501056090780b43d80401051080300040c0c00250088000c04118a81c5080c0d080f03e9040e42c418100d4a490324000354284501d6205110070418814a09003203615850300340380110032100715036901071440d00103401c11220305250143c07403410640d1080b09507621100d083d011504c00e0b00c058012503124418400140000d103000a03a590f60440107162401c002d05010b04215a41c540c3d030342008000750012142284a0381222030344104007103001040c0d902800051001e4455601c43c40d400c420508414030000f0743e0640b05200c440c0110364180000c0366400030940c064403850b61849402013402 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 657756312 1250 657755062 657755093
    0x3010b100f1101140601050a020309090406060f12170a0521010905090d120b040902180403020c1f0309030e0409050604140a03020316020d15020d0b0a0b0a08190e0604 73
    0x981c5048403451340c6600c813080058101d9020f086c1107980320381e9048100d00394418070064581100350a41400200700703040d40b0000c11148001d800101c0b007615040f130040c00d404508005081c4a4440f011071098481c005e0007048402541d0400d00d1921003a4143c00004210001100f00c030700d03603110010400240d942c0242980281846d02608031424441c1c0060030034100c4120001d00300b1340e9500c07401007544443e03026074a041d8005248000ca00381488ac0c070845002d0844044005019143d42c2e40302e58108080000c134582401130341c0f260100c100020071001091119070640400c0106d901315107407900e030340c8540c0c015a401040502100d103080d04211048044401300309400c0d92004900e80003081e030200646481008201c40b40212030114000201180d4250030040c000e4000305c41c1341400d03450950f005005040594005114150300d03041004070310599441005d91488042060741c0c033f4070b441021126844010f288101e103010f0340102640c3c0460f0354144402c98035070700800601c02800108005190785 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 657757562 1250 657756312 657756347
    0x50307060e030312090c031207060e03072303070204050a05071e09210b0123010201110a1b060c02030d27030c030207030b0a0209040c022a03010b100f 66
    0x603201d850011079a40c0c8a001e10590418070080c0c0420280c00341440400e203440c0d4000c04071041081c540c1c0c5c0283d548d521109007110031a14200411010200100503102c0641d0410a9405950b2061412510340859809001014003041240000680d114030803030780a000c46000002c0c0919000402a0041c24080b00d069841c1d140d140682e04965402249002640d9410104840e0403c0c0350318421400d40d11000014040b5001a0020030590300440652100e03081049955100031004001a0300301c5c0d00702e950445010703404001c1e851b652030180c004000c03e0440800f99195003031003a1551411602c4107881c6400582002402c820384900f14000c80500c00c40842c482101c0c098075021ba285002c0c4000002420b001e520040321083c14003d00140000310b4100000062629040c0c0e40e2400951050819a10840c034143c0714450042c8000750511920140b400c0344a00022003003034020504411802e06076043d0740358011001281c451640d0700000c01c0b0141c881c20040194440094960003218601021 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 657758812 1250 657757562 657757577
    0x1202061506040909050c0d06020c1e06010b0307021c0f0e0a0b03151201180209011205071403010f0608010213120b010b070c05090412120209010c08090d0f0c05030706 73
    0x80c141d031503800b140e08581004000041255a515000d401c080343e0f821034960102c0104841030070b2140e1500140b05d6400c28005a84000e103021000c1081c560f450b0300d20f071500354080801880440c1000c80156040301d2240120b8060a8164801c0c1c04580d0000c0c41d400c00003840107071002d000c203802211031442400100d900c001420304015405a150000828180d40403a191180f100300ea241c20b81612070080c040c2e00203015855411854100807502003404a0186502c1400010341060610201c01c41a902602070310615140200d1213801c0c0d8004081654155a140c060f2410320b20940b04410062200b01e0000d130303d40d40201030000001240c1d500600c0504050065330000680c8101d096054900949409840704a00d0a108188a545401260704242d03407c0511080c0020020906264001b982d1030709a0110003000c540c090740100c0441e5400b082d9280242d40000d4003100141c102d0342c0028000c9042521a82c43d4100c0107490b00b4030903a222008071383c0a00c141c4c102440450041c0030031f42030884 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 657760062 1250 657758812 657758851
    0x3150c08010614070b060607020901170607140a0e0f06070b013012050d050408071407060c020904060e01060f061214071b02100e0108100b0306100909050103120206 72
    0x19407601c204c0710000c0c03080065100040890b41c43c84c0c25200c030b40e500641092019078407a40c0c2004094440794554040d440351100140c002c610030901c03644d00000c07549860b82403001c64a0250381d00b040601c40242c0c0000540703505043c54444001a00101b8000c0140d400e82d949448103100c00c81355a0455548441030303110140018100307621040030620388c0f0421100448004200859070b60180f1207014110705d0a18051001f17102001010f44031041c01050444141c101081c4419175903140361150b0300c049174102d8850340140ca46518203ea0180c05400c01062602d4015582ca003154000d4000441c002c41070001030050642c80b4070040d4512040b4001040080001604443c0c1508000c001c2c1d0104908803903200e402040c40c0228003042e0b07074080c0c955486c22090350801360200c0c100901080c005001ea80010346060820341541013181e4250f40c10798510f448840500192054046040080c0030380c00d1000500500300d40f01e41402540038009502011009000c02030130080041d05411003484e10a2449 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 657761312 1250 657760062 657760097
    0x100f08061c0b0c0705030d020304020f0a05131107020901030c060207080a03051905071703190b0f010302210c0a03051807050415081f0510080309061303150c080106 72
    0x3007440d030341c000c128002c55554140c84114035201c2e080d0014824000401d49080481160b00554000c1381300311034911800c254001400300d071080c0d920400f0342c0070b030108410b40e0740e03a07806078400031002c2140b1074021300c0d012898002c80d00301102030707004560880500c0070401000f40c4c10300c805005860600060261514075407001401405808200314040d032800c00b25811180c0a0800c0319440d55104d00419000c0b8016944100950812a00fa08165007003440e044500541449100410074000745112032825416004500a411011111580550300148401726110f00100030b84240c804404036a5035100c3d0520050540fa40500a4070101c941c50050071031004000c01c2d21020344800b81ca001880c040c0711100907064400661000005c5e0040c0200000d03400c0b1f00d80314413506205280003c0c05141ca0b4480350707100004051040d018690002c0c03051806030700e000700081440307840c50103003440d0558072500e5500f0043c1840d0300c144040ca0361004220b00041d001420301e40101083d08001c03002c115020ba40 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 657762562 1250 657761312 657761359
    0x106080d090302040c1b0c170c030709050c04050a0e04020f06090d1205132c070206010e04020a05040c02010f0f180f05011d1510051e030705100f0806 66
    0x81c0f03d05c2e00c940b1001042031003917514a10300385919001d200399007614108a80c091b4a41e00503519100d407140350450419400003060152244040d0081c125240f5000d004002400060880d00724a0000c03c0002000d607101c03000f01c0c0282089121104480c10244100007095840404c114001c2c4030500811400303030b0b0741e07001400c5403e030014840841070301900ca049030684904024500954080040030401200c03c0c03e445901d41c06101c46d4200707801c0943e200316580201141c8650050b84182c0c018072074042141c07003994200c1d10103040c0811841e00c07031740001c0560351746031070520060b035403140f4451041b4014000e00010000c200070821524400040301c0540c4400c170300003c1d021040448110f01000b009601150301031920450807800e0300302000c840d603100d121500c2d103080000411004a00792885000c0d18400b29a0010b1400f602a00440080c1213a0440090700a9042c0991139001419032542000842c230784060ba0340e00e138088944503030080c0080d0000740989000302160a00c8800c20943e0400c2c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 657763812 1250 657762562 657762569
    0xf16120c090218040609140609010f12030201020f0d2705030a03021308160602070605040807050d02030c13060812090d26040e04060609050709030b0a060f14030106080d09 75
    0x907036202030211201c600e842c2440b043c2c580107031919600094072986917210030802e01003400707034044540b03810341040074515084c003500300350700421001000801c1c2d20100d0084694070030f0001605098590924002c690024080d415640c0e403508440c030850020844803140b0b03d8200043c895280b10162a081d50741e002e803030b1011307041c10381c00690100c4445d403944130700c00108590005c944501e03900801103600428184100c4c0d0151103480400b09a940c025020b65007070700c03a0000108280e915101c10000707500703032610040c0d0b01400f4810303400c3c02c9501c4591407542c1c00314005c20701003202850407640034903040c03225002c0a0491410310080c4006d07a2460043c000083d001100c012030703d03040c089603203240401d00c1c5120110200c00074001400b844202e090318443e5000c1c0008000c019035920f000000c2d100201c0d900f134001602113009000003045107a50580002d00c41000281050311124600100c0365640c02554031202c100c00c100c4d0091400f4041d65010b0300d41c003005001000c00740380024007841200e01 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 657765062 1250 657763812 657763829
    0x30614010e092a13020c0a02040e030304050c13091209030215040303090e0417030112151407080a020d180b070e0904081c050f070f020607051210080f16120c 69
    0x24219842e13581d48000f40c400840e00e002e02156a0180d40003011b0341d40c50b86142c220f00407410a00681d40e0500080180d0f445903400a01070000a010708080041d91848510061a021703503608245001c105492849001c0b40155180c41c6401425401080360042c0c0c041c1c4508005e00d070803c0240000395002c1000d1045542060f4201d106483e1072a203801e50082501108094040c003200018941178940041c1000d0713401418407031005624020b181041e5140719400c3c0c000c14644030007154915104008003030384140e4192005041404200000e016100000308a04541c101c1e290260300b401400c100030b035004842400c1c030000c910300e01004554031303da0040c070261480ca8003046103030326444004c52024000d090414200300526100808120120090300c80c200090303020814105041d000081d8607001d2403242d00da440c14400603500c20506440c000f02000001200e05d000001c07486010003000f081c0e142000060544507810070b40c2c140340322442d60b220340307111900d149980003c01e203031030301c1c0300305864089 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 657766312 1250 657765062 657765133
    0x2901171006062304080f0709050603030301030f0f0c050a0b0a0215070f2106091b0207030b061201111204120e010e121518100908030f040507030614010e09 68
    0x1400340900d038001c0e17500c078803480d0007600a113401009000c2114015070301500b801700416207406080c90354034002400028a000c4c2c071502440c0128240302102e81c08248603d848000d400d4442c8007080c20711440b5844056540c40208400010a8060001d03658040d030b40c54070b0113000c0c070307180c0f100401690528811000f449a100d90b2445c414144400300b03480725016031021310855076902c60b60401070075000003034140c0008a906000482d032000c035000049075004117800c80d09480e084104400c001142003c45529942c40400c284074071840d0020703086442c520111411645002d0420150300030762060300504025003a4000010340c5e070031050350707400c0c2d04040d0b41000e05d009011046a00c0c00e0100802031144000101c1009840800440c1d004013080300501541d0340b20100c2d01c908410348010042c020994402400042c2070801c00e0340405a119018800f200d81c00c3d80d0701d894040c1107450080b07a09500702804801400989540c002440d000129403000300a02c8441c05c400d039088500040c2e6121001140 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 657767562 1250 657766312 657766367
    0xe1c1203510305030a0c031b020a0b0313050f030c01140c030f100e0a060602010b010e09040f0317100509060a0302010c1b050402040e0604180f290117100606 69
    0x11141d021002c2d60f40401203a50341d41d200300d80600340300c550781d20440002c0d042025982c4403512000018844550181c00e8009449c10a290341c91240c000a046550300390b9030700b0131400400e60402005201e01190f50107186c1d81c010f5004400d0035a10299110500601c40c2018802c000d021107003100d601104059443c105501c60044000000f22a40d10980250400d5002d0103600c40039a40040211040c1c2c0d00200191f00c0c0303100040d5411400032416036130003008000028003242c19021503d828501c43e03d40081203040130144040314000c2610a02080805035009110a0912010841d0810000c454021030a451079000a24810700844010412515250400f6402309102207240182000030029511917440d0340d22100240801c0340e0862040c0d0a0030380c00710005555103045280c4a13000390462841050503241d81c181e50100300e02035610f10948500b10000c0403400f0950b03902034a0400117103082588003203502c9250183c1c102051000a00e050001c0261603041240d000c1e04004d40c0e0846422a0721 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 657768812 1250 657767562 657767711
    0x3030714071a06040606020d0504050d06060b0403031e092d030b01270504111c08070b0906060301110a0e010507050f060117030403030e1c1203 63
    0x425600900b228038036002c60030304092108500d446070304192401c0080380da035020100e0341c0e0130303141c3c1070407020460412082c0894101205d905110314010100442c00c5580d9452a07941c50384164000c0d000117000120210041000304030029600310280761051a03070f4100581c0c2c4586500f04640740e00ca608441c11b01000850310b03030386903c00554106218820943c4e646088038529660100110305d00c44108903040149210f500c1450f0096800003550801d040c94071007801210101d4003105008400c180806500046036003004141e014411004da001d00c3c00c04400c6146807002c09011140b180c0d040c01c0030a140846071000f901c110400038906440001719090041e2524410228080c0c8030740240700b5006110080051100d04840805114492440007090626168000c900000780007400703030944410989402c6210503a81c12a55601264a0111b9941c10205807005250030380429124100520020081c03400c0404c08a60006819681c036035802c00c0e1821542d881304800802188400c030901d920340d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 657770062 1250 657768812 657768817
    0x20102060a023a0f150303080403111209040623150c06090f210409020904020d0e06040201090b21090a08040306060302030d0c081c0e030f1314010203030714 69
    0xd6510100c00d4100c0fa4049121645880c2c107600e51040742000c00e400d9a11000f0f210b8042290030007101e83c0d05213411580c0032680020060019410031a14070401104508140a66254a0004460300d075a0301490703014401664404d41c0203910f407002c0a00c03000c60b14030400c5603140e03082c070b01142d04240d07012181807002ca00303004562900e1014400c400c100074500c100042c80034058070b0001e00302c030b92f40d086150640e003820000b5041080706203014041003040f00310a4002c0c2120440090001d401e0510180e501411a43c8081200303807103510420510040d03581161100020340b00000c111482c02c0c1c044e180540140465800001c03148070f00c4000606240b0080c4401c044466001200c55a0b4541e42d0a000001d06507600041e442030003002d412160060281841981650348000030900741414004034070081540b2a0103006100c0d1035541504180205200030702c0c0740304158001039201c00502008507440c0c2c0b80d580100c81200711000c0301c40c48a03a00041560303071143c1d4a180c90a0800028240c40e40c090 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 657771312 1250 657770062 657770107
    0x501020a140f1203090709050c070b0702010b060f0a1416080c030d020f07210801030b070c14100b0607030207050904031103030106050408011406150a090e070201090203070b030103020102060a02 85
    0xc2c02501c16154943c441c00009600801c85402191078540e1104403842c03c031001a0303100382c2c030307010304009540020b0001c542035070380070416000000300700c08440c01041541c3e0007150300f454000e50004440800711b800000d0003010003007039000d20b4100105036039500c15124440c4800b40808401081c80d5104407820401c50f0484451110159141c04428400001c0c1d40c110900848200305001e101044810740c43e02c003038142030000d1340c40080350707441c44c1c4a031460f01c84080c10602c1081040420a408100004800c140700c0e40342900074200c0c0080640c21400b21031454000f030f171144004200c208082030380020000181c5400315640304c150b881d180750550754218602c900c3d0007140404400003c9442d0000c000d4411100c00300024000f03841200500c00300078604403005030b4480da000410745c0c610500c001c06031907403119a040c081140e6032540740c800016001181e008005079161000482141030510401d40200032200c2c201c0d0465055078000b0707460341c0c0020301c0030500b1940480d28107070708560040c080701403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 657772562 1250 657771312 657771343
    0x315051009080d03110306060a0c0203060c0910090e070e031009030e0a050612011809080309010b15070309050103050709030219170a050a0b040c2408010b040501020a14 74
    0x240e284000340501901000c0c8a40c0e601e9000d220341442e039260181c0950341c0e407140207000ca140786554540801c00d1540101ea1110200a041d02102005841c02c0080c1e6000f060800002c545404003101042141811021040100140000e0800c00c002e401400c00f038228419041403a0090b00d41030210b45050010103000a145003840e490340c05050b0801c9407196004820307a5100115611042400010b100c0c603810b44461100b07100042100c164132820048050600d070313001046644640e11090902d0304107591608807030b55601c164001500c0d150100e003000d44da0302c00c12142050b80740c0d20042c1020700c01d48034450515499000050165100301079040155a0007808040b00c020000280303003843c00035004000c4910f00008181452080000d44031000d2648200280070007100b0b55286505131030098000c4442c0d03031034000c011034001d0a07904079440e01c40420741074031140840800010407001c1c040c0c3c0240c2c1d0a14081005000c0f44c3d9001c5141001c01c0e40050111424a4140b04503516006e4480415140b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 657773812 1250 657772562 657772579
    0xe0d02031801031401151b0f17090604180605150301140310060b0a030c03270c09060303020307030e0409110d0f060c03020c100e0d080903070515040308070c020105040501031505 78
    0x100100e600e00343e86030180866480141c00c00007191f401c41d880c944008080c1c100c5402c810900c3c00a141c1c80700308201803c1e111000e41c1019040700c0440c115130000d812403240990341001100c1c0e100420f120308002000d00300d580e215400c40d0303405403a58a21042c00340050b90142c401103010311303407030800850048201051003081800c1d6038500f040d0860300202c1003040000e082030004011240310780140710440c44099044a0000901c00310340200c038103095030807203100684580024040049200303200003103000b80c000d55941c1c801450010302c020342c40c090940c4124613181e04d0310702080004240144546056429000c13a0200341404c280142e08400300924003410009295035269054000c3c02d0030382600c7c812070b00e40b003074001840c009aa80903803003504203070b000007621195117108044241e00700346010b0680f4a010034039102c0509204080c0100320310a1964010b110415500c0165143d10030310380e18003507590182030b5000820b03500c240d208a074101600c4681d03500000300410500002414002e04112 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 657775062 1250 657773812 657773819
    0xf010b030c180714210609040803010612060803121006110c0d1e050d0905091b0306010c0506070c0b060402090d08090102033c0a090501050a14030f0105040e0d02031801031401 77
    0x10400042d0120300c48170907200380301240140c140908050301869000301c4050841c2c0c01c10504a41c898541e518407244c054480c0710000306141c0074030041c80d1080303140c8404205072034441512007205880d503200804201c0f40c64204001110b000c68095858032013201c540125102505040090070600813003002c000e0759502c5220704000d000286500d120320f141d120110742ca9a01c204100f0342d29012a01d900d00b05480341d00301d01d01c000c45e01004541c0300e01c0505040300702c10340716180d045c980803044820401081d0780840c0c00051015040c45607600403802c031002c0d0300e444107180120f03103100d07104000145804004240803905d6070007171040d2010600c428680f40740e1a03030f01001a464042525803a040c1e1071074540440c0790552001022907032940941d480e144c0d02e0601d4040111219440020024100040301d50346040103c01c0c0c2c0d000310702586400c2440140c95040100b003100311010b001d03801807242d201c1090501460f402005031601c41d1595580a88071075882d400580c060030f1078900750313a14680c1440012 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 657776312 1250 657775062 657775087
    0x1d1005040e150108010603110706090305040b0c030d050115020a0b06060f0a02060f09010c0c080a02120c0109030f18120f0501020301030308040c060e01090b03100f06020f010b030c180714 82
    0xa4000b5242640c80242a907610282070742250b20078241d00c21a07190401c01100403d0858203c422124800d242681c581652050030000c241c111f518409541d0300001002c071221000b0703004103400b400620300c1065100c226484069a695041d0710000c2946c21550001000303555200c05442500d40f501d20f00075624511410001c1d00e4140441d510240d17040c0c10004a80e14000510800b000288103032269a02038030300d501c541a954000714070180c11403140d02c0d21030300900500005044540c21035400464802401e03e8050010200c00c1c80706000c2065503207585000103000c6a02c04101d40c261309004042861034100f180d58039500c040050020b41c0004000010107074000c441501c038078010060003d110b5161a800c5a1500c204545c490002e510b00d0301c18410904101f0003141c22000900c9003044856499050400da0301c226031010000d80c008150000c1004000c1c09501c00500c0110040d001c1081c50100107900803846030345855850b290b2000184a05000301c00d090b042191205407283c4517641d81222 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 657777562 1250 657776312 657776341
    0x601050304060f1e240308090d110d0f110108040b010506070204090606060c0b0108120301030b091e0c031203090307030e03160b1804020901080f0a090c03061a011d1005040e 76
    0x185c103511000a0305103240100e030078411405032a030246045180046000800000601d4404140d51008401c00d0b001c12969074007032810242031048001107440039039070410110140c0c2400000707050004550821001035000750085054a40460741d0319122001800402d000b000c00d11402000245888008100540c0080620010b24420103210401d80e803a519150389880c4031010041c3e170160b05000610008410b1900daa5000d00c0a40840c0c01c5c2c3c0110f844154241c20000c42c6140180e0000b0f400e01c0351605042c00b6403c1200c0d5940c021500e18240441040d0b0b40c0d11a111004e0b0400034000309840c0c0e5640d040c407001210380807001034544a00d482d1692101e09070300c00c3c0446200340000f0f415003041c0f82014029500c8404050b100c2602d139580e0f00394101e0724180c1c02003c02e080c8a644a000c2400650308401410155000d00c1000400b101f008001400d500341c0071076203e05201940c3d2074008101030201c2e02c400d001006640440d0a1100c0000990740390290740c001200d0310740e0b008100410060384026 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 657778812 1250 657777562 657777581
    0x81f120c05040b0a0b030402060f0705032106040e0604021201020f0a0306060e0d030206041b050d0b0906010f03050604200904050c030d0e01140f040506070b1e0601050304060f1e 78
    0x404104402e850020090706084c98850901120310600004003d407406038098811f00740d00002044c90050681d544900f583d100004400c0c1000701c00d448000100e0102c44900d5001d10705550400000c203812080642e10305004200910540302c1e002541c02440c82901030360a0840c074500035078ac9504d180c0c0006806001c0c20f000c0d000018600141942c2545802a03140f10030a4040d0003410440d10395880f40159403400d950301002414682c8000242c540700c0d440400c010341d000c1c51000c030190612f51992410a207060348198649502c402d41400892030100f4540d8029510104142a054040420703010500c0035107916a44080307403804000c103004001c201041c4441003107040e20304042250400341e5104110400e444c0c00280c0c4104950229005040100007502e01c24084a00b031540d44c00004065034402c0d402103545021407414803008408452580000c1006401c031040c2500d0080002050350000070005025151110820304501d85190b00c401d07a078402541c118200c0880540f41c03d40a02260075 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 657780062 1250 657778812 657778819
    0x20304031e050406090e07020f0709061e0303050418230412030e06011403070b0a0504170d14030601170103050610230d02011403040c06030f0903081f120c05 69
    0x4031070a070314440c50031a0103540c10782d180c901307045007030401010080350002c241106510071050301d160002c0040201d50010180ca000c04501e00e401d10b901032014011702070385488814981901400020f4110b81614180d50310321941c24014212011100f01a2208044040c41c2002075055003012980501010780b0481c0102800143d00f09a042c0403411203a030803a0100d480e800c02e00c0103104900c45440c281c0310800000b011145019242c1542c0c103800e03840b000043d0b02141c4009003c200c150a0030414010652003d000340c070316203100e100003520051a0184200002c480040010070350703070141c00307101c8038507400c1054480950b841e450406e9030341d02c0640e02254101c0a142c0b000074144060f00d000c03203601c10078a020f900d10f81504c40500c0314031a9022000c80c140801404400c109007001c0d405188524011703524005013518150000e0125522100822203072800c003502c00c0c02298114219039006003d420011f101240d1210482040c8200c0b0740240801310b1188421505200404461070141d40045 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 657781312 1250 657780062 657780107
    0x31312032c18060d0b0903040305150105031e03040303080a1107060b0a170c090406110c07030b060a0506090d031b060506090f090709050907031a090d030e0c0d0501020d02030403 78
    0x12942d00000342d00880310180c1c40440c0100c800005940038a038541c001101004490810740c8a644090801141015848244400200400c44c0389400c206884200c09010390315845a1040e9242d1912842079000141c14402c3c50300c081460441590301c94003004403554203041d190303526450114003034815003806510403d2a15400300d0301046a214900144031501c0040a00300311f01000e100034094002d0081e90300c01c6c0d65440546413a08280c0c010003219074400042e0014505500c2d200d23a0500002e403489004030b00060f420700464461408903880a0000c540c042e4071031106240894250003480c500301d21000e0741c10000010001071740c001a026005c100c0b10000c5983c0d404101a40340c85045404c1020340d17100c00d82c104081c00e440c2d481140c12111420030b90349a641c8a858042d045014109541c0030071101404001c0001070920400d41a0706151500380a005028140f1907038803400003940301c4c0320320120178002d02000400d6046071156000360600b55100d103064200641000384000d005501d80038030f07 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 657782562 1250 657781312 657781339
    0xd0306090b010f03050a02071a010807080c0d1e051f06090507050f070507050a06080a050603010507050d1526190b1303051612020d02031312032c 64
    0x103806041d900c014103a44410862800c3e4508034090100541030100c4c003a401c00051010840a0360340c0c80d04402c1e105860749095141483c0300e45800c0c1154030408054102d443c4110030350307480e44102401c071504540524502c040c0e820340b803100100c0c00781c0014010300c141d01618410203400c241250100e1950241086001e555001d40380070340300300701e03004000100c007040034804c920213941c003030420140140c00325510b081d00d13500031403404104c54010001280071803041000d07c9601c0e004540d84042c0540c000c0c80709086c4240c0c068001e0041c0d402c140702c000e45035400111684c00d40c44505004207002070780d00302d01309070502200b01c84641d007400c3d0364080d000301d0501d181e001c1c541d004c085405130703070260500322250b581058801900c0ea24044c00c8041110400c034040c900c20701c5202400c0d0403402848030503000e0136900000ba107003001000009080d174000b030000340d43e003c040c0000c10080352001c09510448110324a400c0700c1c60118103d1030403259038149540082d440382d81e4003510070340c00b05550611a0810 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 657783812 1250 657782562 657782579
    0x1201140610030603020307030305130902030f0f07020c09011514040902450103111206041d0a111f120c030203010806070f111b1327020f060c0d0306 65
    0x101d800040c6d0036900c0310300c00704006841640240801c0159503903046850740c8690418080c2ea1060320075140c03201e01001481004203001c030300386030014102d0005103051082e05020030341400052050000f07a031000109100704034044c2e80c2c1c4689800d000c0c94a20703a80c0340c8640300d0000940140801340c1241181e04a440174403900240f00a1458281104840325941d445c1c1c07088403201c0e151030865040513203a0242c51080107214000c5c15100d46409000800b9140c0f15040c0821142c0500c03a10f01c294040d202c0012035117401280c0043c2d0190071000540045005102081a000c0f0f0164454080d483d5040006071055215000700c00380c008091080c030903081407680840607400203004140c0c141e0810004270710303004c1c09011300c0401d8060700c0c01d00e000118002d00a030f0741003402000c0034507140402050380e041d2518188030310110110849800300102e540c44415206088480d90003e2801a980504081076541d105002002c8003402800305030341e2101401051344a140c480403640202c0d080c094080788009 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 657785062 1250 657783812 657783821
    0x40c020106095912042309070e0409050109020901030f030801230603270d030e0a0f14030702040f020c0c030d0519140f07020112020423120114061003 66
    0x80c01c8481c0303440402e659145881d40d44225070100f8802d1090b2050490900080c1002d0030040c44202c44803130419090f004005401201d1a000382c1c40f8008040800c007840d42c00c03c644252038081694005a201824a003c900524000303401951190b540700c0008101b0030131030320000710351303101c1e580e44042640d1710000a100020100102da2606400210440c4241004405194400b40f1550310700f00d174201c0c0300144001101d81040a0007282c00c00707039840000304d401d802005003500240000300104602d0b921410403003400054000c4c0740324403058149014442c100180e4031655002801048003040bd100c51030002d500580d40400c607802017201c001d949180121354070746400081d4403603d140c040300c480b0501d4141082c500807024802a904d50300f610705010f40c0a0644503007280d0301030b5520035190002408428014280c0d026180c01007005101e403010850342442c2c40380d03001d0801c3c51440c501c900004d100c1004610301ca080c079072825082c030541d04100030b4550b00070308099654880402c25141c04900740d5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 657786312 1250 657785062 657785171
    0xa09031112070f110a030503090f0906060f0a020f150a0507020a170f0705070e010e012403021e0310153615020a03030b040207020f040c02010609 64
    0x345010700c0320b07402003801e041e210f194071441880c8600715035099000144030f40340075030026195640003080100340d03803e05407107808848108450f126a0303850f00c1e00010302148030714602c03000a10000319108228038002c00504022200c1c00382036403080b160002e1203404005086a0303080502d42800045580d541c00465240d84058100911410800c060500508250b00c244040c105404007080850007050b0107102d12030181074018000c00740365240030580791015106801508140c2c8a54214028212040c05604009078040c01d0150b02d0348150313088101d06e04e5915640c4a0f8059000041060f0400b030540103e09594a400c0381c610201340d140b1007107958004900a41d010002001540c0b10114501c24414180c0e40725020312050311a20f6400c1c40e06060380001303401015901000c4218101034050088a500c0507058508504101090300007551052001e0740d07250086075543c8105180c0c9200390000d102500b10503005014804650b450100394420018940100d4141c1c5da2034205507110184108886 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 657787562 1250 657786312 657786343
    0xc12030a18050d030917030412060509010f050406020702120f0c0405090709020f0307020606040c08060409170406050c01140114060a09090f060503151b0c07030b0a090311 75
    0x904140311801d0350110790085210360030280184000805a5807400c15802040c800da40781d00d2940e2600b881410011405200b202c0c9035002404280002c25054030024403680e00044049442c2d1600c0c0d4a030b500401554244540445c107040412080c0a0300d50001c24085100751200146070003680342c0075403954010040543e00e5040f0485270f03490b51406420080d00b241d01041a1001c0c0c1d990740110108980c0268090f01d000c003004000c002c2c0b4590148815541704e81c051301c00388000305203c0c200610242008006134401c030780d507070610007d10080d800c046031010900310051340c0c0c0d2a160000a005900118860242c13903007007000141001c001e14085a0403a460502542a086480782c100400b6800521104c01004100080000d070f0001c1e42c090580c401d5007079800041d41a00b401c00741410500511701882c51500300d0f8080c00fa03440210a500002181d000c03015a072201010194503040c28507550018044845000a201c051a501d40c0801c2c00f0a01c6510b40c00e9022400041c0c03da00c1da611920300140 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 657788812 1250 657787562 657787567
    0x408030114030c030102071110020708030301031202013c090803010608132901050d050d0e2d0108090609060f0a0207020409030e04061e0306270b06030c1203 69
    0x1c00540c0403241503074007402001c3e50b18100b60240400e0883e0061801a12085e21001d207a1826061080341c107001105144003924955090000c031594038881131000512800303040149241840c400c1d4089103c2c5030407068002502600301920001001080f00a02c03072907072541c0c00e500c2d0031841512a10039400e0f07210300c0395800d51386008801d5a01890040c6941080480ca400150000c0c04000300300c40310850701018211101460081203011071b10580005000e4101c1c80340750320210740c00044a01c9aa4458600000c100701d10001254641501950a1101248205080034008072003020040303003490a907102e215682d10000003075624030040d9106182500944081507545803020240703a80030255850140c074181040d800b050890f210b000302600090382060703801d5124075003030140d0740013842a8820b04007a2102c0c0740100d124404070f0f1000500c1c00d980c035000900d40d03000344403411181040400040c1c84400c0c05017000c0510300c0c011180207100e4003a1200f50640c0f49000c030300c101d2041c0d800c0c0000b5070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 657790062 1250 657788812 657788819
    0xb0906010f2103030b090a0c030f0b010e0f06091806030f0a02060f030705041a09040b0406081b2b12090f0504180503030109150e010821190e090601020604080301 71
    0xb81d030120200540405444d0030446816403240b800c9240201d881400025800d0390650008048a44080081300700c6c07400d10b441d00910b030f80d100d1103201181c0e60032207038030304000d0700c0000043c803074428010180d4102d0f400803c1100342008241c00d803441035106806403940120751000341511144039001c020b501c01420301c002c0c541a000700c4040c0d64418001d08000c3d15042d1100510303204a1600039090984950000e407044450505010f007050f815800d48090080d203083ca450380d41c65030030000758a00300c0003840d8031418690ba0307103203440340c800008040c0d101e8003083c4a06105100c03802860060b11200d00c4031445c400c91074441e0390242c0445203140c01404203241010100000752140700c000f50388d42c0202c007050b080403420a00055008003070500d400915019200b000030b2803100585d104500040440c40100010200442c034420403c100701a2445603a403101e5200c003d600900c821950441082c150300040c2c940c114420881c280f20446884981b540e600f00126540c140031600207004132000d00041 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 657791312 1250 657790062 657790109
    0x10c1706151c1815060e161e11061006051606022b06050301090f060b0109090c0203030f09011802132702040b0117160e030a0b0906010f 60
    0x40011002031110444a032448000c840b040da18001c40380421a070038200d90070104111640d818091080b4040c00340138040c604407100c94a10300040480f0792002c0f180ba81001054801c02c0d019901d01d841090001454244060041c10b4030046000c05e401340c401c120106403001c1d11380f54114222846640c60916017841042140180d901039041152031903020310030b449451841000d00c9807050510000458544c1c0c0d503005100c00d40b40203034001c6000c0e9261140d054040b4110032640a1003d4001c080850f040b4030b1500101c441c001542e0184035a203181c440411505a4040010340c024001c8107000c2da01a01c8402d4480e0880f00c00101c01d00020034204074003401402c0c01c00314003190000c0c5180000d410300243d040031190090b034a144100c0030040a0aa1085152034400c507141c4902c04c0c030300000c403000d03030090140302a030000c0e0002404003400503903041c6039486a10351461440b00030b03054441b101c0c0750303140c09400303100d05590100c02c0e401900e0000c07034011062284681114400e5040010201001848 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 657792562 1250 657791312 657791317
    0x3050601051c0c14030a0515040b0319080c2406011b110102031903050a1d12070203010204030f0602070c1421070f080d110601050a0e0a0e0f010c170615 67
    0x40c81c00344080300b11004c1c800d100001c0075500c9004008400b0510740307071400e070b040b400c05d41c07100382d5500c928600507240380c86843c0003c461500c880c4a8460048a085038104202140601650310300e40348158201d00c003881c1012007038550700d294250310958a603100c181c01550410340d0412841046008420300101044003900b01c218002c2c0c043c01a03a1800e00d00884420006014200520200340c403801072011040070742c410014021a94800c410740c0803260420b03203442c0c01c028410011104004190311040d5502941140c000350752121240011807014600240a9080030b20181c411450814000441501c0038160188108004100894900003109092031103050707801001e810b4410084041141e0444203103150103000c1a03001803191403091000104007003607128100ca010340009004005c1c1d80c50f00800c02c8140c48001401c1e100c0d40da01c20412500404141c1c22003400c900c10601c01341c295000651000d20030035210341e134006105001300c400564403c029141280c014525141c11075001180714007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 657793812 1250 657792562 657792581
    0x609060f03070602011418030a08070212070609020111070b0f0a03060306050c220b0d091b0b2502060306011b0c03080409060905070903030f0c0b1603050601051c 71
    0xa40c0003020803034000300b46810215000040941e40d11305015040c15409030025a010308403003000c010308000846090784070b010700507007441803000500220740e03c54001c1c0074910300500005402500ca6000d800c164015265100041e03004c2224039450034000d102c045183c00c00d5070000d450980c03411a10001300749980d40304036581e40400d075a60a01000042c011700a1502403c4509400c58440a0905103540040403240ea048244086e40760204162201d100075504081c40110300014010074034104102c20b000c800d0302100090f90003880c0440c05031a1800500588030303601e0613005a90085481c4800c1d0601c152074043c0d031141c4240700055140d0f100d01403032800719445000c40c0004014555810710241902d400484003207a0209050100b00b400344140710060502002c04c0c0705c6030a01d117001510080b4a4007010b42000401d010680541d809203881e01c4600c4e90041c400074032031030f0024075401001c1c0480c000c0340000b810440840d0032588100141d0b0303411000720310940180c0700100c5106c4001d108088 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 657795062 1250 657793812 657793819
    0xe1b2a030c0a0b07120f06031a1005091b0c0a12030212130f0c030b06010813030c150b060a030e011a0a090c0c0b15012703232b0e09060906 61
    0xa1504003884001e000b0310b44c06c20851200414001d0952800c8010300c501c850710100c14280707007410407841000304000c180c1210400c0e94014041d0311001010f410981c0022030700315103501c000624541003480007540c400ca140c0500340c40400441c650000320103034816804c41411024510011451140705842a11041489034120500c1d11001e540c030300c2513203507007a80309441c900c192008200140d44c000c801558081031070461000d000c126603801825030343c00341502030400003140003980c40c0800185d01c1106c26003801007040e030300d070910803d000307003e0003210381c480002d5403c22181c8184603603450141182e01e240240011845070070254450010204501081c00308800e17a900170340403c8840100c02e008040045000c844203140c4000506824040317140c04e60541802010704ac1443c000c942d144090386da00032a0744410310328a400c54091800343d8180130442d0701904e02c00c1002000200e40c0c0c4070400f010000c1061300340a00c21005c1c0c89000001541540007103040700090100c2c5031424484d030303010700c006 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 657796312 1250 657795062 657795077
    0xc0a05060f04140a090e03030103110d03050a08060d170c0f1507050d0b09040c090c0806010f0e04090c090905060c0702010c06020307020114040804080f030708040e1b2a030c0a0b07 79
    0x5451074801d6070306c40070394000241c10000050091081c0403409280381c642c00e88440a800a280e41d0040c407920a44506408100da41e0002c01c1142c0d44403144500c1c03c98202020340f00410b00d00441480035840b42030080d44910031005580e40162001c1940c10a4080202c0c000d459940d405400790345650000000180c080c0d694140c841c196a540ea84250003140281c0800d0929030034007000310202d03503605200d8000d0010407000c020301070f0392048103019200700b03e251000c4c18105110105010345104400241650010040450701103a2540100d6109007c0da00b211a162181c0c150b003207080c03003110340c00390004003141000300214801d60011604042144000182c04070301e0203c034881880b064600300c4810900203000c01851904000400f6010000301c06103260821540c1da207401ca201d2841074000c01e074558800140038036541e0328200b4a002e071074000156079680c040c1c0c1e074481d000e00f05441c1c03202c110750a19000ca64008000240c6041c05503200041454800c50303299042d092034010491810820300 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 657797562 1250 657796312 657796319
    0xc0501081306051003170c0705190e040b070305010e07090b0304032a050d05040b04030609020402041701060f060c03020d081b0406090e0711060403050a0309020d050c0a05060f04140a 80
    0x2d900c030b243d01c44c3c400044805041360a52070300f42044080211500030303102040c4454680e03500302064a004a90707048660501c2c0c0c4841091242c5850000d80c800792850604070200310a1140c9884910f108440036501000300780c0e2070798800e0342e030300b541070755100e0000d0020a42407100020801c01150414040e0a11841c412003140c00a0503064012140c21494892000903908220042026900e03000c0315040c42418103061461254880c01140f00142425031207060017030941d10790ba070460740030301040b542c04110703101c003010a1030183c0483e1240f40304c0c80b2040c1100091440c030442c450001c0c25407607406043ea00c40008021a418803002d011711040c0ca0185212810700c821020060004003c540c68a5400d50314224420280d020024160780034041e40c00d0300b41d00314001c0844d6095010b40e250801c030342c5480c08024100c0081c0741c40200250001040081c0cbc038188000000c01e4840e06038220781e18081030340c640080c40450700844030100458041440140404040400340c00074a070000b42c000d10403e9035 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 657798812 1250 657797562 657797573
    0xc1e05130225021801030f0507060503011a0f16030513080c0108070f020c0a2d080a120203040905130b1f12020303090a060e011d0102060105150d050405010509190c05010813 76
    0x1806c5e4003c9410440320518181003200501410700207048a003031182c2558903062003c1282c1200710300c4da903a900c4002030795098445a05c002c1c1e4041108852070185a1449450054000d5021821041554a00105c0040e003241c001448066100301039440811030b45070310034261007c96000c4d05000a40c018036403d20981d44900c1d07407074401081031500b041d250000c01e80d00c1c000100c260603801d2201c80405103042c0284080002c00b1080a60700080313020301c40382d8a210403070070f41c0140e81140d03081a003840d080c40f1a07803510b08104d40030b46004030b18001c00c1ea19018140e14427940c070310004031440050700c1800c000301c44201010307541c214005015245070180b83c6c0b00051440060b6000742c80403c0000c542e10b101540d0105000e15826031149800214100180020790ba8010500c9200c1c032070000788648001c1c0114403c161406121280300c14021402c141c503115001e000d04a070036815a118440381c01e881440041c40070080340d6002040404c10b542803400440b5007400c024418144d0404914280b0000740c0c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 657800062 1250 657798812 657798859
    0x9040509011e090b0c0f0d0e070906060c0c15020106052709060405030d020d020405101d300c0303030106020d1e0512040c1e0513022502 60
    0x5009100018070900380b001d41c0b20052041410340842545441c450000261554103c540c0000c40b01c0307280c07515012090158601c41c4581115924803a007082030040683c0c00c0002d030181a0b40c3e000d42e05000b2213440301070850300140d01031400b0f80070003860400bc025001c60054211741d102070f14400815000c1e200e1010507159155207a900881c02d40d490440c00c4d11682c84c0d00100d4200c01300401915840c249074a5081d50390003600c21603030303420760f000403511111240e540c11a40181000307010174140490105000d09441341c00340070303407200e0740301c294410080d450415603c107070007449064045041608070343c0e40c4104002d07a040d8403803140300e58403015540741d0382000914004c00107540181200d42c0d6040c2d0040072031903d140104c1e40c255003a05880e000c01c0e00441500d0741c0c05405c00c0c0409042e035032810b00701158080c0b580201010300c504a41a041c40486920740c000703071a8152555114000418001012441801d80051030701c54800c881602c142c000c8078044207454001480e0802510500722580100b1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 657801312 1250 657800062 657800071
    0xc0a0317060a03030c0b0a0b0a0923060a171603081b060f181005090d0e030c030c060a05040506030f071206080d11030f0a05090112061a0c03090405 65
    0x5028000a814103900003040c540c0e200c002601c4094086103150ba0151007020000001170181020310001002d90040d035001c5010340800500c2c21010b0750392440100e005088c9500c41c2000c80da20a91202441441010b4a0f0302030840603040e1112140b401c4048200079950201110702c90255586014549078040c18031001796000d120025954030b60150360b84a826041d0130700824603000701080002244811100325400700740b0030b4039105600c0c080c1417000d00744030980740d0304a541c034130b8038045c403404120011309140c109801f5200d6521424140c000c05550780c1440320001c0c0d055000b03040048131410300801a0648041d01c2c1003103401c142e1100b0000d03074103400807242c0c041402c8442040180d410b501c0b01d112040c28030794810401074a402c08100e5900d0740c03858040c000a02c00401c00030003201104004541c05061071150306901c5074441c2400800310b51001142c6030014501c0c07505003407a444144140c408941e00340d0a40034010034644042c6e030312604141e2a01c1d105001c24441480152602d02890388a03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 657802562 1250 657801312 657801317
    0x603010f0b010806192606071b150b0d120e030304050d110102030c0f030a03240306110c010e0a0212030309030d1a040c210b0901050913350a020d0e060c0a03 69
    0xc08420f51b517030303d000402088441080440b04400408070305003840d024450b90400c11500102c178a0641201c0034012507404280c020a0090010080c040e841082e20044013050741e17120329210a04040698a02950044d60b610428800030f4100184281d0140c400410044c010340b800c10180700801c9040c10403164500f082600700087ca4445207a26110b03240581c50349039a03462402d10b2031000c0c48040c4041c0d000c0207000540e10080c0241015264040d200c500c43c4000090203c2c4001d101810b03110400034500f240109000d04002944403000700030b80f403240c3e101e03030007c50800812071481c0c4054010038410b0105a040c1007408485a2214021001d01e00b03400e441e00f000d42d640c2c1200015441d007088502005041c50000461015900d8130100b904481085807141900e450ba019514007100361100002c2c079860101c000c554201c3d035601d4011500c41c400300c001c01d0a400220900403401d1091074605e10051304101c071007000083c0120703c0c1b500a0040640703942d00346002d02d9039951401d00e040740309401 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 657803812 1250 657802562 657802619
    0x6030503070f11060301061706060f04090b091303050a0c1a0106050c060601090627081c020c0414060d0510021611040e06010e0a02120403080603010f0b01080619 71
    0x2801010b0250f0110400182c0340945513601d0054020580700d00f0701013801c1c10b00b0208000c00d6a560310b10080c0c80c18000008070b441c1d0340d0383c0e49401e5000181042c02880340103040c0b0000203661440030074000c081c0c0d140c05813a000c0c600200050103c0d0f140800c50800c403a40030b500055080c10040d40c0d00d03880e01030800e540b9000d641c2c07036035646070f03034a0850024025410010809801d0041c2544082c442100c983c4c3d040900010045204c481c4043d5015900002914441c65103280740841031058420845d460940a070f510102d1040107000c155400c2f200402e410081d040003007402406c0445000813554040e9040d51f0210540e444c00b607060364003019034440c031100004e20180510001583c8001c2c0d00000311010881490840805902c0d070320144159480f040c50000040e020030070300d40484505160503100914946440d00d07000e45214000d558050080d0320b400d80d66921380f5498890001140c1d8140c49a2a25940c1d4500f04042101c042020003205400300b900041d28540300c28040c00034a1240d0740c40305 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 657805062 1250 657803812 657803843
    0x140f101a0405010e030d0f140d0c030213060c0503090d0201021e0615090118110403050304090c120207050c060c0a02041802010807080112020f1f231e0705010603050307 74
    0x100004c0c13220550910940140001d1154150450521510100182804407800408640700442d41c000d03190442c64203401c0c400201540c40e8982d00030941c07403900c2c454009040d903c41c0d02c1201c401c02a004002c1c4568003c101c0c000c1140340400c14004c507244148101c40c860707501d8041007c1c0c0d41051120007031031540b04400344068611445140c0c071440c0c8003a144005e0320342c540410f03503065200454004020b40c0d517a030703007903c03085400320111009584c12404491750b40703a032030f0702c01401800c0207450303040055800f4040c038104100d54000c80e200250484000c0004020303090400c89207274442d0400b560240300710030000c00161118000e06400710810036070010bc640041c00050400e080c0280800c7c10004110018030a51010400700c415541e01a030300c9240e60340700a0041030501c0c46154114060b03070b00300c080701d800a03903100442c5940c0380d00d40002c648011901c4950f552840c0145103960180303813082c0c000f4000034a180d00180c1a80d5001d5000403030701d56901e40302d079811940410b20540e41c2080015410 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 657806312 1250 657805062 657805067
    0x5100602103b0d0509180405030403081803071401050d110d0f0b09070e090403051c0608030c0f06010f05040510031406040309060c0b0f1810091104140f101a040501 72
    0x100786043c0d007414543d2624108034001401d164409092815840300880490309201c0104184c2e8055a4460b0344103030749d00842885e4800182901d4540c40c03003071044140200715030070165502c01401d45c060f100c1030b060204038001c1d940a0710301011303545513a6905001300515851603005145030a29040c40000394103505400340030b030882d0010400400c0c00394201110703e1a4413805612030380160149070044d100d20164142d00da40191564002c42e59034108880401e40340004001006e9a0751203078110742c0d403406550705880d141c4000f40300b41e00c2082c00d1500200010f040c140c01082d400301d40b07080c3c030816041c2c0341d80d11f1004140d1443d00d0500b041d8803c8007040201034205001c02e002d00302509080202019590301e030005141c000b400030500301c1030a4042000c481b40c6044401131080c1030403d0380c0c042508d002c5001c0007001d0150b0103403120508690107524500f0b1505c50f001c08034100d02c0d540303603c43d65031035804100c542001c0e0044500c0c0d002c1032030002c2c0401c05e460325a00344c0c01d40154001d42d11440c1c00c000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 657807562 1250 657806312 657806323
    0x130f0e0d120b0d0206090d03020307020604030b012103020606130b12030729010b090d0210020f1204050901030609050f06100e0a022803200a0305100602103b 69
    0x68001c1c03034043c0c10303440569624815106e424408407034103806056186012411400f99403c0250040000304000c800c00a2102005041c1c464044250090060119007003580225068003d009a0405000300d0b03ca41000309001071b0b030840b44400404e1030080c2c100440c104590880d03400f03808c5d82011905100300311407810001617600c0c02c0d07104081c07101c40b012995885110b0600c100d50000c60300088502140c0c5940c003264a00d2600101181c0000c04683e001035291801124a0f04181c02100c201c40c0b51400c01c8000e45003551805040111141c0c01c50b6210402800106000e6809100c0e0240140d5000001c1041d00e20130180c003034148026502d04850003001e064084d103400c192600521030b0307031140880001920b40b036105030b449044604c420307403030300380c00400d0f200d83c07000350112500b000c42c4182c06030300006101052480d50204025a00c4240c0d80410100314000c8000513003040003075034100c100030303044030003c0305500810161500f584008050203013100c15149101610030042d00c10120010b100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 657808812 1250 657807562 657807581
    0x1d09010b0a030c111005130f0c18020a0c0b07030e030a03020405030705040908070201080606090a092306031507200c010311160b0406112101050d02130f0e0d12 70
    0x4007014000060303500c035500c0b07002e0381c548504050f50361400154045000108021825000401e541d50f9230303a64145070300070000d00e00030050740004c100c002d1040759403c0d00c01c50700803000c151f075841031883c03244e03461a00b610405011042010b407202c9130580070820a20082c030b1301d00b0941c0c8005940b00e207048245420001c143c0d000d103204602d00840440407400301c00c2101ca8107542403801c61910381d10200003480b5401380400c0c01d43c2041034500b0104116485510050503046c11890602c11840f031911003100c801801c44480b909904508500e00030020003820840c0c03c800d850400241c5d052a00180e07145d51600c100180000d0b60110720f55048958040c4560940c04008031f00503032400d05030aa801403908218000100b120301c50304001800d01c400c550040800fa4600d030030290f42c0d04000400402020302003040c1910889903100000b40b5407400c403a110a02d01ea020700038000002c202a841e000030031b2840c0703951300c807603441b481c80c100071820030712074104d082c0101c1e10b41c1c1c0480c0080100c10021200c2904 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 657810062 1250 657808812 657808817
    0x106090b04030f1406070f1e09060c061407020a0201090b07021c060b09040807140c010f0522030c0e1302090601030b0d0209010e070e0a180c120603051b1903031d09010b0a030c 77
    0x11101d2114070350042127842526441c4c20260744880c802c0ca08100108030030003a40319812041c0041c007901c10b60100d20810924001d81c1c40001c103c0e229030181c4400d12401c40d00030741c001906825464030040134082d0030340081c024030002032920102c0300403410b0074400701c408071a0f102c2e000840708208011070265401c8005a10b004140d40e154074070020713100395a220080c5051101c041828030000b90b804403a4a080d41000000c00e0000341c3e00c0c60000710110b1940118018004010000382d850612002d074015902d8004110702c2103912510015002000003800c1142c00885c0041010701585500700054001c00c4160503e501d01c3c90000002480c0d051054031303d03881400c1c0c015080040c1003148040c1421481c40c3d400000e144100001c1c141c0c0d000400d5603540540380c4c104400081444400f00300b40b03402d0448102d0a2082c4a403410401c840c090060394419613409003c50244082440359000b0581c0c01490741c140d5a401409100041104409034030481803401c00207401c01500b685402a040c0702c02460 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 657811312 1250 657810062 657810107
    0x2030a0f020a051203100801020d020a091a04090207170703080604150605030414070e15010f05122403100204080c0a081b0f040908070303050106090b04030f1406070f 73
    0x190340f9191502203050040015640c048041001800c4190b5201e000308a10802195182c00d4102c2c42c4011350000c00d135000c003052650100041113002495003003091280201d8151a007401d21107201c0081d0401032040d03410503450b0319003443e9802080010103049001e45c9036074200b80381c40c07170422098a5001800800020203104100409500201601c0e04690700003186c0990840c8001c1c11490288145d20141d05040e852080c00804108400d260b14a090207907981d41d00d801d85a4030545091051700c3c0702002d0396424030b0014014802100410030100d80c0301881c89070345a9628002031400e902d110111841c283e00150400060b6400c004200341d0481c241d401ca100c1c50702d490fa00039104d848180c1003150216500080c1d801650390301d140c1200041008000300031440050070b18540c00d8004440440100f4034103c00414050b020f55641411610184041403825045036240313010522640c0084400d030a81074600d1203100c1040c0150b40c401c9c0481d59544203141c92420008200c640400703403050140380342 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 657812562 1250 657811312 657811333
    0x50106030c0504022119141b0f07030507050c0306010e0f090303010e0a090c051e04060801090203060705130e070903050c010903081801020a230d0302070f020103050c09132909010501200d02030a0f02 87
    0x9c4000341e80006401d4100942c44181c281440e030b0a000604152581c107014020020035407460b91003807940103500848080c401980c1d002080c51307a034807082c020381007841140700004448002c00d4000002e50751080d00c010b441366a40b01d002c244201100342c5504a460030300780004400e03060a00c01c080040281d08000c1c071032030501e07402003515442c0240c440420008001010304404c2c035000e2051004285072140c0d030b1198941200d0080a040090002300c5290003690601a415840f8060910603203400c1542d1500e0032a0910051201d90110642a41580112181c0c9804140d038214000c01c0940710800c80c0300114603200c600d80c103201303039000f500c420700d84180182008594102c1d106101c20340d0a013000207031501c079421059070a0164240c0a94080e01500c0c40c1703000741960b5009151108060901c003480190004500c090f51400801c58a0b001030092004114662046084e00400560043c40b4400d203054046268288001c1482c0c42d8096400080c0a283c0242e000074500d2407100c1500c06000350b80352 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 657813812 1250 657812562 657812587
    0xc020606031203100e13050f01090201031a0a0b1b1e010509031804091a1501030e0309010c061d070603060503061302101119050106030c0504022119141b 67
    0x2485e000b440310540300640040e01204035250702045085e0840112021060354011030340c0608800982280001d0900780c00040c0c68220301d44071207904030b0040c14200111300b001c0e0f604030780c1d802c640301216009240404402c42003005014a80d100c00152980c105864200d4440f1820342d0070107000903800390b0003000746e800011100894100f0201c801c072004036010125080580061585602040404030325902740200840001c03c01c0c00b044600780c0b42401102407410302240c80b03000f042549800314a1085024001800700d601c2011070451540c0303484000d278030040140e031516105030800c102090b070360b05040c0180d1501700310450740070301c00c04a501070b29091640401c2c040b0045207003400500140020307a142c500001d025440543c07400c1034100c0c0d265075440c2071460282c0010b11080e20000840480131a03907080c07500031181c180e8102440b6401e00b032400c07200c224401c44c00070041b40c03558240118641d01d4003c3ea0107241c5001c2c4104018910a080c041a1041401c034490701c0008040e104110004a140 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 657815062 1250 657813812 657813841
    0x304021e0a05040608071502030a0903080c0c0402030c03090d11100b0d0c17071e05090405070306021306080105041803110f07092703090902070206090604090204180605011d04020d0c020606031203 86
    0x90784a03037665100e61920281500d005000c0d14525070140c0080208443e06503040041c3d881030305181d0840c1c425590154054592629000b036410b207541142c00094040b03001c0d50020b608583c00901408000691034a6075243c20312641c029640711860030030014480b100810007400a04006040c0e03000c070f00c0c0240704070008a4003501c81e20b400381c220000050140801445100700440d086034040d95601c1450744088801c100c10f00442c00441c0200300045000d0415200d1203164440b203540d03c0d0180c2002d5141a24254040c2ca03c0e070700988034a0442c0c2c440701400740142402000c45103008214040b41281051400d50071400d0b804900d420f548210000c2a844400b24044420003400165224618008905107102c2d040602ea04101c0009000840380c1301980200f0460341821041e0840c0c01c00300040000b90759841c8201030010303002072042e881ca032007000488040648001c000600d4031800701d5184065610300840800960420401c000e00d505091141c410000c0c6205051403941c90482c1d010340c4e800 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 657816312 1250 657815062 657815069
    0x3020307023a02011b0302040f09060b03152b031106070906120f09050709050105010c0809040b12010e07050906101b0204060803130f0b0304021e0a05040608071502030a09 75
    0x20b400807203422402d034000e512201d20a004810640005480c4400140282d402482a02000e030000b0300001006542c0b445201b05441301840c250740365403610140094041000002240e0000180d06030311260080c82900414120965491440512190078007402884a402c1054001d030080410060f83e954088000030a0b6902805c0682d11030880c3c03100c041c018640f54600d241303c10b1a1904480500c0030000e5001c3c21204014014010350381c0368401140d400c070358401c0c000c0071014240b00c0392100785031039009200c0002c2c000d8030641c40c41d00107501c45803c0da001000801c6d00358011003000e20203410300728040e507030200c402d5541e803029190111009000ca10001c140c04540c5008034003010455a440c2c0001d0000c0602c0c5048a80340d61107180702c1c1071030020078462802d4140c2d0004001609072190001d89100f65001080c01d0260160308081c0c5064130312052605130310109502010919545a00c1208054118a4028081541802e00d07280c440ca803145140020341d0320074028440c82c81e0b07200e500d100c1035 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 657817562 1250 657816312 657816403
    0x16080a030c03020c0312070c05040b06040b0a0201021e0912190f0c050607120f020a030804021908030d0b0306090601050f0d03020102120a020d140103032307120302030702 75
    0x580d001810b04904001d424403107103905010300c008108a00700704c54081c02d50789019011311000d00b642c0700104003c40d030141d125039403c1101401300704888051079014001014a9000240c6001c48071010380707010719400d490b5207440850205a000741070924000703224061a281008100020508a40412010701c8560090007008007030a1042007200842d1550001c200c0580080d881c1c04651818005540e58241d0410024041c0000300e0011440001c13a03019080d096190460541c883d50240002202c0300b1440d030300800d03415000080d5160040004254040c50000d0005808096504060912101802a075810b034003400050100340c1d51040c0c0007c2c404c0c0100d540c2c249108040c50181e02a00500070303031111100f80d1008200901030f003500140546c0102c118100f00340900c0d1542070340807200a0001a0000303941c042121070300f204842c6000f401d0001c0004060418410744d903403c1c024004d000168000071307008400d0041554042220f10510055100c8060301040120080901612410041004e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 657818812 1250 657817562 657817577
    0x3010b0702010c0b0405030c0f370218090717060a0917030406050402010f170109020f04170a0b06090c0a2609070315020c0303060d11030d03050916080a03 68
    0x210ba00070056412583c0d0b1001c07440d1014074240c02c0040c1c5036008000405d10034020176000807207281d804100c140071140034052041d03004446001c505015000780040c1144440405500030142c2d4801001031496803851044c1110307480c0a1410f241420f02541c000303071003041c04080d0fa400240d000314016070f000400329400602030304541000542c1806e030030302200c2031820020902c41400f4054002038442c134000e80b680070400b01c8205044464480001204044030643c0005220002c0b80e60002c00740003100030042030030191240c03c00800034000c00134480140c2d10071100041084802c0c4543c643c0710004554482591a01c400c900d0094880c1c49601820000001c40c00c0e4040c0130544e030b10000500310016003540c14503003014504e9644017180001c1e100410020400810b186003402240d14000800020f9402c640f107510070311554400b005011104038146c00e9100702240ca0400c0f4601410355941e401040361f080010f0340c44d0078181d142074001a05a0740010500c1512000074404c903146130300d45011107 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 657820062 1250 657818812 657818827
    0x140f0405040f020a0e090105010e040b06100e040c12060506070c0303050a0513060309110306091b03030d020307090f050102070e0601321308060f060d060f09061b0f0503010b 76
    0x9101d5070b00720020342c01248440003055200701070584c2803050461400800035640c907013038511200d08080303c0040020708250002001c50816a889032440314250602d4041e250740440024283d8800c51142800103200012024006078180103c1e4020202600da051604a0f00d03141e00018403d540405410304c580068002d992034804c1046401441211490000c62601c40d10001d002e410340c1c52082cbc4460301c10550900e400d00c0c001c00c01c00c1c043c594a80003072040e480410b0901d10b1001d06007981d580c3c10b00040c0501e140440c3c030750005500c0786503250b4804607624200301c0310011304406a0041411540070301401d009040041d290250460000d080aa0040d800c401c4030044040e0f060b0760080c540541e00301d0b44005aa065000b4080101c21920f080400603158014507503104401c50320f50380d01084490124445007000d1001e0030141d40100d46c0403488003c80d2204c08240c9028070021642c0540c0e1708090301c0703002e114002c0e1132242e85403850040f5102c90050001450740c0018003c00d00070f02c100081c0003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 657821312 1250 657820062 657820073
    0xe1605090a2c0c04091a030a050606120102070b07080a0f06060e040e01050f0f0405160303211401060f09051302030901050106050f0a0818190c140f040504 68
    0x9408111000700502025a116540100c0d60703015141c04510007905444140b8001180c1c1c056244200001d5058a080514041843c0003170040400800861034205c400702e00720392400d2041982080c0a034000786410300707281c0144040790301381c50034192090348144500e40020302956551078100e005807910000540354075540c40000c0000c2410040e01900e04080090016000725100c604110b003110300b0040c440f07000e07018500340d46013111070600210f5042d001138481d11035900450b4100d80030300d088809082c800c00656114105507002500031684181004d0410024051a1161286075041c24000401400d04024a08078103004000500103481040c007040c502c28000c2d4402003030010901d51084480410500c02544240c8400303007194280800880c80d40c0c000c00460740102d00d100700d15440d145080208480d41d00c1e01400c04155010440c640c1c58150746c0800c0142c0141c400800d81c3d031040728051408400400c8140e0041c0f4104041c584150465603443d480e040c511002039a010038181d4441c03502 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 657822562 1250 657821312 657821317
    0x51c0c2001050f180a0611060a09030905090403031b0504211b0b031503060403050d0b1309140c01020607050406120b0607051006081f0c020c060c0307110a0e1605 71
    0x3c1c108000e2011542c0b48981c01600324200610074241c400f10207850311260304036480307210710868400075403010340810641501039203c0910f041c028a800f035400e944a000051000a059030700f0380010740c4968445020a082801d0480354240b40e04045241134a444000c101c01c2c050000c05960110302d000807941842040540c804241214540120706161280e440744141c0d0801d442076442161940b040c0f07a96828000385150242d605030711410305084c0b4141024002e07141c51039400c4d4100c0034000b00030103020300600030788402612403407200341c0510005003201d03d8510b5280f40a0304660001040c443c045170018116000d40c1e00500d00031004060140c02400603111400941c0c1e0807000c00201d5100340724002c02c9050030f2107000f10007070045c030341c0e01d5010690301c0b6181c03120180401c1410001c040c840d00342d0307401038415803203500554855006510010388285c000c203c1c0c40c00b8a40000035280c0c20040c080001090f5481c040b075806c40010b04001d030300303000024020003802c01007100342c00c20f51455005209 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 657823812 1250 657822562 657822577
    0x504110919050a09170c0c060a0309050a030c0219231c080307080907060f110c090103060516020303090c060702031e0a030f360e0103051c0c200105 65
    0x10184480d0400c1d44110f0010656010b0030b489100c03082d805005403d0316001150242020f40000303240010079001000307002c0d805101e00c0e42c00e2554914030b40b40014000e10002d8009802621458090390f1103005000701104109098550a404054140a0403ca0030704691922080d05010400d52083c0b0300807444a1412035444912105007c0d844801c00c264070000318800c1d03040c3d690b180c40546850004645c2e4400c1801240041100c0100180045100c0c02280c000c5013190022500c003400c0303441c08180401c0d0b0030f810580b280f5864038200a9003d00034110142e01c0310940c401103142d49849000c07180c8404441120602c00c40c80041c10a00355075003006018007160115070b0284102c039150304c03820b81e900c241000032000700d051500307240902c1c0c2c01200b40fa0b08119824098040140b001144c0c80b184015448080c1803504141d40082654109600e8036800380d4480c6c4018552096000c0310040c0858a82c1c0301c4900308030b541da040e040016014200202c0a800e4645500502040b03003005a40a000303290 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 657825062 1250 657823812 657823861
    0x3090606230109151b0b07021e16230612060901090b03030306011416140f010b18040503040510020c01030b030f030a080a06091104031505041109 64
    0x8001003040c00c914401c041c82025007404408404503100c005440036546072082c890001c40c0007000d103802070701441200f09132901300c0061900f4140242d81c1c8100c04035003690004d0040e03102e000c1118441603032548030003001020030000c1440c1c2c035a4040c440030701c103240e0141c41620000d40c1104c50445007134210302e4600043c020302440d21000348120300c03841e800307040f1222489111f908000144d83c215500c40d00700c10080142c003462a50740c44000665030b4510351b2002c803035542d00030003180c5006040b20903448a014801e1170a40b4034400f40824003072600040301d44418059142c180505c4803a80e9000415a0011000582101d2541c070b03410700c03605600541d846250040d450315104002203601098100315040b00340c030b08111507001102419a1418400d4582000f54400c200d000504c0d402000c070107038040c00c041c0700401c10607160340f0094203464025803000e500200100b014400c1105400c95420050030444042002d481d058880401c40d0307214410140c05207000c2d401003000d00356001c004444001c010b1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 657826312 1250 657825062 657825071
    0x20c010615050a091a030c07020d050d0c02090c040e070c0302010605060a030f0e0a080a050d0b0612160807051602130e071809020a05100216031a0105240307030906 72
    0x400340074210303502c07010240703001482d940004241c000f07585c5190381503c1d400303403103d038111750701c01050350b400d0b900080c026030b07000c01d94a9000000640400c1200e032600d52a55440c2c07104070640c07051040d485000740842d40c1c148000d0000340249901c400c0310fa5802920342c58800e110b0082800c050380140001d1300107503000540004d02444141d01900301c0c203402c01c040c0c2c00c10400108850200d503260046040300030310106d01040301c0341083c0e1140d4060501301440c041f0024038038080720b0004485900200c54003038161418403c01c0f1400d10b900481c0c80301a00d21f401c010542e442c1030f2500070840d12840c0ad0020041d018074a40c0300c19520380b920300c08440d400756070080048007500c00304151342d201d0301d114100c0003070300c2c1c10725031881c0c10350034042c000001d030780900b09100890414082040d171051200c101b208611488235840c0c40b18000748130382402180184003248170b5a030b81d0000c03440000f1058110074090310b510844010460310514a141a1101d21a807098803629044821000b401c082030000d028541071 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 657827562 1250 657826312 657826349
    0xf0b030c1c0602031303140306030d030518060406050a0b09040f0602030c0d0903020718020405060d0c11032809120311070906030809030d0305010b0717070c090b150c10020c0106 78
    0x74117490300c0445002e91502c41003a045006607403540c1c0310484d44030b60590841503030718000d64003940245400c0f110880744070715407100b43e0503d1454600101c0b016100303039480385e00340b00c0300d03070b00501c078110900f081039480841500c1d164886c5c00810082c0e034402405241d0000008422801160558094400805051014400d1410001d55500c521300803601000c402d4100840080120f100b280d0448401401c281e003041d20400c0004001c1c50302102c0001400722244200f2441d440a0000304030201c20543d4603403040081c2c9115540c0350840d44010000e005a41006011080c100491404e07180ea2500c2c10040031500c1942c242c2c00c000c140c0e4400501c01d400d00b003010081003088030280a07510400e60480380c1d01d80c88076400314181c0340e0030310443c0048001040440085020000b40040125100d914586814450b61794408041386c03d9005041907035585a60344403516050711845460064451414141180079a1803a12500c07039001e00307005542c3c0001c0041c808074080d00140010403098924120700c600c0d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 657828812 1250 657827562 657827581
    0x408070201020d020d0f0e12070b030f01061403060d14030f07060e03070807020108280b030c012d0e040510060224160c0c0303120f0b030c1c060203 65
    0x24010480c058041d844200c1c00e00e0348002404c6200d00042e9551640080c00c2140c143c03041c890310f600701600245414840d1844180c104204401001034420040c0e4074600901c21840c0ca140c1a0071400800c80706540060380a00c046096035004078007110b500c0b940603101e00d066800100180c41228180c0004222038080c0b43c010300240c00004d00842d01840006034852543e82c80c1e1280c800028031101e41481141c0c050352003554041c0d40040749420340c859000c0d0302402c403009040c00900003a01c450319040c0301003850406000e4004100b5082c02c2c2a00c51341c507200425081200c01031210751070a0494841c090009214441c1100754000103401001941440c160000405003075010780c1c0b000d0b02c280800c1c080d249245285601020303000303141000b05919181074070641c1c0c1c2c0e2608406001c10026105520108a40c1e128000003503109841d91000c0b5180051640c00f80e80100341c2d80c030344483c5841e606004540340454001102081103030b0b000a40134441002c911110685200a048244048200152070301c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 657830062 1250 657828812 657828817
    0x103060b01031503080a031d0610140915060f0915090301060605040e04060f020714070608450d0305040201181d0406240f080609060106120605090408 66
    0x100e080c0d8052019900b03400c08030035150010b22009100100c2048403417030485c8260321640c0850f80410309003d8030300002c1b841d545040410307a04401040140c00f010005900411b40d06500380c2001e0300c2014851424040000942c8034007a40c550040c600021480001c4140c10121109a5001007280102d500180e64903c4035402542a8500070b6282c42c6012030058026010346d02111581c0700103107070b5640d8996900010f00304607007102030215000d0001800280400d441e00a03001002c1c130003040c0340f070314000c030042038000040d110150701c1e03100b458102986544510140c2821707604a03190442c0544501a45480e80c410401c0c04a207809100144405541d060b04040e0140c1c2c002d130782c2c1c0f0021452540d070f01304075001a842000319840c4e41e0b100d00c0310240d00c2c114034039500c02e01400001460311984259034600030140c6075108090000d0500c148160011194910041c10300303100180310300d01d010b1010301e80d03509041c000e003403d10031012421204d01100303800200c0600009402c400e018181450000c0071038 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 657831312 1250 657830062 657830081
    0x9122604120c0e04120509030a020904060203100f1a07170c10060e06011209210f03050136020c0a060b13090506221b1505030403050a110c09010306 65
    0x100030b540400116446401c2c019401960051014486206510002d4a0a521641e00150180109080d80000d607480403040c521650040202507587c0c9003440c0007401100da141c1080700403103c102d405104c1c071040e281c04c0c00c00ca0404405002c4c1c0e0743d009030800342c0d05020f01010581e182e0382c0008078078000c40808540340f003090131014030030b000d600d4079001c00b82004442294041d000940c01d0800c0d542100341d50700580074060240011920749000851440924604050740e41d020910300f000c002012545841703128010902c0c4003040c0d98403485501070030b042802540c404411513161034048040100c103075049030300d01c4251504460344400d4500c3d020000e400b202c0d041320b1142402140007644c00b111401204903160b4003030054405a55110020f9621003911480500e0041c180600380d000113000002c100f403440c001c04513400c441032400c141051580c00003404031040250920038000005d4004c000d4034103024043c204240b0304212550320906d070030003060000c1d90190f00710b8000414410036510041c6c0b071 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 657832562 1250 657831312 657831323
    0xe09100f0608011809060b0904030203130602060103080a051c021801030b120d121e0e1e031602040b0d060b040506030a150203060105191e0912260412 66
    0x25607900020b4855203401d100d180c61001c014003440100c5100b50b801010010b205080024075184070102003181100100c9040b40986d100041c3c0804080d040190301c3c4c000e1196200a165644c1182d6a000280c003641e0000018032501254200b260040c802c0b248240b4020984110f40303411020485003124507540c041c242c013003440d0100c01080c9041001040c80c05844500050070803101d200307411645000c0080c07039440030725980c40b81b0008180030036180c000c0c107010310000401c619030742c07048990900040e40c03280e100e03c010b400c510300d140c84030200949a43c41100903024030102414000b00d070107400304003202c6038005002c0d81c0341004c11079140d112250940781900d0402c4540ea4030814540d4503a50140c028040b104281c80c4903013290b0503074000f141c0c480c50600d801403c0076154014140000c104410450200300400140e6007030307440b00e40d1010300c000614904680414030b0700c050039443e10700140c800742a09201d43d060503180c00d030060100382400d0035052400d80c0c80303540c0c1c1c03090503a012912108a54 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 657833812 1250 657832562 657832589
    0x20010e0907030f0b060a0e0f061605030705100b0904120504030b0c0a080709060203090613080604080d0b0103020a080402010c06110c0d1e320f07030809011a100e0910 73
    0x506200c07054400050847c0c54859103400ca01e030800c4047d8001c460596407000c400c0040640b00482040d8440380d1030310501c02581c0f070b8001484c1203400d2030981c101000445240c00500c540b16030310b01340e24030381113501300f46000c103401c0030010112100c0c03149401c06000003032000d06002415010000500502480307980f810b2041d01d070924120350608135849014016030040c009030380f403850014001c0c6040080344e101e501d4115940d04202d400c0c5501258240c88041010070f071101500d80b140100084210246000c40c9003042800001d403240102030400382c100061104182c04000890703010003d040d99004500d612130400b210b03000da440c10342160700c100054150f00070214112a280312000b0240b03650720383d0f071010080403100c040c0584040348032450b0490041601860b00012200415481e403003124080d07903421180c2000351203101e01908900090303140c0281c11520f19004448260420000c443c0714900c2c03001e24904880d09110000b166602a401c43e052040d0700c00082030500c11104024034490 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 657835062 1250 657833812 657833831
    0x90619090507120c0e0907030213050d0c0e070828020c01051819110603060105210109050105060909070302210c07031e1b0c0b07030801050901050d20010e0907030f 72
    0x203072400305c0700000035045074001e00450803650081e0058400c03181459001c000c11381d074801c0041c5c2141010402588c8110041000307200c2d038050b0903880d85d840714803400c2026a40c1007443d0b6010329040400204e041d0700c2031510359201c0074070041d0111940047e10b040240240e0400b81c1807810002e0b2031580c005010701c11008401130141400203000102604240710307480c0404c4280500810780d100415560402c074041050543e401c4101d18000d40500340b50f40da240349907051800580440f003068100d580300303c1e018082070500d50f85403500760354440603d01c0d02580703510f83c207104085500746040d50300e500c0003222000c02c2080941400030302803603406a41d03140c600d02c8103035695401f00e84c081840f500014802907030036210540941071410b1614840ca030858007003030341c446242ca4540c03c10301c82200010b07520300040010745403400301680580b4049031030012502076545c030b01540d0365840c0390b0704400f201c40d1a03106c4420382c0200c0c07042114410190014006241400f402001000004c0b060341640745885101c5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 657836312 1250 657835062 657835067
    0x803180c1c0f03051b0c01020c011403071d040617010c0318320309040b010e0f011107091d0f060411040515060a050a0201140402090619090507120c 65
    0x308891080e10710081c0d08041580b030b116802d980210043e03081c0310040025070b40c0700c2c036078012594030b040d81d4501801d9082c07030720b074002810302c1700040045040180200d01585220025411a40c03c18401d0405403000724205219002800b40301c075146034014503001d03000684082c460307405100d200b80e141c020840c0c8502c41d941a8215001c0000d5174603440101110071000032291142c5d402c000c008503080d01314100c40070624803100c40781d0040c40071442e000410801c880d82098064072015140900f410704103112500003141c0d17281c5d011484541004104091051551030078440301001d8070006605011041c4003c0c1001c1804180d0826010a841000ca21258a800106800307000c1d070762000c0124400c5c02d140007040090b21015000580080f00e40035070811a545920044c040c15059440d150340712010fa9101030b086a4808881070040c598034010000140d4600d000d0b150301010484410f400841a000c0407904660b10743c111489407403414007408105500301d814402c080c11a09400e102c0c1d6a002e032403c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 657837562 1250 657836312 657836329
    0x90204081e030406110a020415050111010e0607030f02120403030914010606080106033317010b092e290702100f0c08030a0c030c0503011a0d090803180c 67
    0x42101c6400500c024443e507446100c40505170040704088821142c02c90700041c04584220056482c1c024072070004020070f50304035108103e914a110000c01c00541003c01d03668444900400306000c0550700d01d504a031801d6294141c490407516a0350750303405450146000b900420b0b8694068488494401c500480e045050180c4002d0312155500c100c40b40c0d00c2d00d50305501501402e5078507500c0500c40c04040303c14501034054030b1010f10000321540c1c4007c0c40d1908003410740c5600b40080078943d0420080c9071090300c0f050320300b40d0021000c3c001c0300810303540c0c0c0ca42c92008600301085284201c032480c0001481c3c1510300000241c400c61000e4056201c0380381d020000451249043c02501b180ba054001f0585500441010384411407608005008812a644185903984100d84089a041c0e40d00c0701388006036814440c60311203a280d800e043e441c650400880d100c10039100c01c00318111010006004540182d00e0b0072801801c0da10151040e101d00f41140c2d400b810400b94035412040e0710840e621030b1030a2030030700754 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 657838812 1250 657837562 657837613
    0x180b09151b070201030b0105072010020d090b0a020106150801050a0b07050c0f030106091103040c0f030c091a13090b150d0609110612040b0112030503070305070e03030409020408 78
    0x1c0d25440c14a1a500540c042c10a140403103061040920402c0081074241da200201c01035210a4001030070f00b40c108000c03200d02c03503100b034604541c0b051503125050381e000b0010710141d880140c0b10507190030b40300a049014001a801850b010390b006003e00d0b070380030381250806058940480d040b0014584440154807a4003130000060032680c0020f0001d081820b2001981c0c02a40000e0000b00d4510780316440700040e80d00442e000000c0000c0041000b0902c40e000011034060244040b004503083d1031926270f029412000d000302c41e0b00564507140504251012400d2681084001c1c0c00d500a0309103404121000b0310001001380c4200c2d1200000580c01c00491200d07108101004003080c807022119150b200040111010451390648045e00c251b2403a6501c1c0f02410140140d10142012454107151036035083c0030680c880c2208520000b4240002a005015203030311401520300002c0a40d0356100071140e05c42c8a000e001c0c0c240c0030001d0041080b40d216001041913540900480d141071500c411141c00c6400c0110 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 657840062 1250 657838812 657838861
    0x115061b03050906090d060e0d0e0306070225080a080301081006050307060f0302040f121a010302010c02040209040902090415061a09010f05070c0e01090e0c0108010603180b0915 78
    0x4216422490440d0117020300500150210320780004954500701120300d1051a1341403540014500a49241e00c2403585500380001c0e005030140741010040656606551260a8003118174011440352149000e000480100000b80031100680c482d401c1000c81a40300707024000c514000d0014903d50003040f400380c04103c0e0405001452410310b4104201e40b12810b6220b918101030702000700280003901c0200440182c03103540d141620003001440c110991151a828030007070000f0890041000d81c1c1c010082030180358041c1c0380943d45140700c20016000b8010050000c3d130004460301400240300c0040c444800c81d181c038542c100b00003621400a480d100e1451310081d10003070300030800e281c01540305406090303a0080b24240b0a007440696030310050003851903040303030601071086401040201d4650090211b2203003c030000c0c1c142c1d1541400002c2010405024900c02d064444250694504889000ba100a0342283c8000c1c80307820010503941e1148004800c80e000c0d183d030320000c94851415540100c10628852 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 657841312 1250 657840062 657840067
    0x504021311072a171e030910020d050729091b0d0c031506050a0801020903071a0d0509030f07060203060a0e011d09011d0c2103090906120115061b0305 66
    0x4950001300420400401c00540500070b2034490b4808550a03591158204001840c2c450100e402403050b00f43c440380d076210455016484c60601c10f030b00030f4200c3e8459500b200c40341071207000d510701380d0800c1d1f04e140003068020a45002005132466022803440007250004150070301d80814030b0100101c0c4031440c40080d113145041300041001031244100c0035a12491b0142c040351082e40d5200041030701d815a0300100042e5000121500b03036240600410010b0404400d00f91000c1010081103006c9000c2c020192151598500c0802c00002e000c00641d50380200d10414103960f03840038035054000e50000e8805c18016020307004041010030401d141241030343d600c0ba6400c0192160101d404911407009022900155a155050031001e640c0c0c04181607060a010001c1c158080d5039014031084400649503a0645803151420101500e070120494008040490300300410341c0322000040c0345030744000312500581d07107000a420b00c6a11130304440d81c1200c000703031101310380f102445003172003211307141c1c0100100001c13000c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 657842562 1250 657841312 657841319
    0xa12060b180d061409011104270902060d021e030f0f1e040309060e04090201020d0c0602090607060e0d030e0a03031e050f06030f1603060504021311072a 67
    0x14000e25600300c8005049030340440b41d07600c820080301d019080341000380c02d08004000c4500001d01803000f508000d80c510b68640740c540701c0b190092481c510700e080c6c51720b10142c40344200020550444000c1e9500281402d60741c200f8030010100a50140e40410314582c0010444804503012000303a910802c338900700d43c1e000d5038078018a900c00e00c03001800700090090084241d424001d04586952040e0311985030842c42e076080c150302508600d074a4100512940c18000e01c000140d0f4003184400c0319030501d05080841f0301140c617040020740100d48003607800c60030119480e03080c41f034141c110341007400e901c0083d10200540c8100490607520102081000d03580b100c040310000900c40d500c500006d407103405448141c410854001c0003650825a41910389411020607c2002e203424001e50041e07664040041000141d2200d034282d02000388d100150202c1d0781c600000c1d00b9919000550f92088000d01c208025140200e801d81c0501e8101038010f461000c00d00044a8000c2415040c132181080e80c1800b0152091a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 657843812 1250 657842562 657842587
    0x19030204030803061207080708030d0e0c0a0b031504021914130b03060d0f031e0203121f1707090609021204061d10052208190519050a12060b 62
    0x2c42e04a081a14486c00100040307650040c40444058020302d00510350302c040d250a1003081c0da222001d40305580e00041102c1490743e03035a408404c201e98412044503165519050091100380c12a05101c2c0c000e8000a00c01e41c4082055a1480b1541600d07180c81b48030700654180e61003e4095800207000d40c0c610070800380890804440030f544c1c0158000c0030000311740701e580c0e9507404d50030311020102d001c5036040c40c0c90030018450803286481040148000c0d818041d180040030003942019052020300b45801c1d00c00242600c00d0705504c0041c10b5a10064012108205100d964a04462007002200c3d80b900e400070945040030f000329034044044d8400121a07032a20f41b682402020003400c8148000c2ea4080c604101072024040c46040405102c400185441d10410034460407036603449001200c3d1810210303400007240c4030142c3d0041420210004e20500d40d6402c10b60f03031446140e41155070b83d5500811186e6550784203000304121981176855888000e00b01e0100030075a2058003406d44480c50500c9400600003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 657845062 1250 657843812 657843829
    0xd060e0601091403100606050705060f071d0d05190605010e041a1f15080606090a062a060e0118170a0903080307030b090708090d2f01021903020403080306 68
    0xb80700030185c6202c1d4030a403121703d007120340540c412404128081101d50501c6800d11800b6403140402c940140b4600c3d00c20f0004184034640842e24803104450180c840d50f60304d5568640000d954410121f07082c1c140110780798107051890190494400d4100300000c24401c0445581d0b901031a03104024042c000b00d071300d108402d80c01e0b000300501061054040c3c1e00c0c0e6407042d4180d03e04001c0288003c040000e200300c0a000308182c0700100010b02400b420030050400e9191040c00000f15922440c1c2002d00b50441d0010405040c21804500c00020407041d0f28004e04c82580d0206d9401401900200f0034802c00c0c19080c180d0040003940606026180c4c001164840e0b0048002d02543c09945044a0581d40f20703640d603601900244d4071000003c3d50791200c6916810f100c038060740c00c40603d042030350440c949414002d40c1c070f40c00700641c003003000032500030b1403820448085894151401541e0610f400c010b07182d0290b000307400c41d240035010115001c5069604600034401c40d01500e03042040d0b00c0c5980e581d0002e11006a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 657846312 1250 657845062 657845099
    0x32212030e10021617010c0503041e0515040503030105090609060d06150f0f060206011e1a0f0a081b120a020903120301030c141e01140408120d060e060109 68
    0x40c080c413201c0e808503060000b00c0300003804d440d00b000110340c00300a0449007112003501c4440c1c18801c0810520012807100c00242c11032162426008030880704925000d810701c64081f204000c0041c0180501003084404809541610010f42d990b440560780c100070045044026940030390000400d0703200d2030201d034407500002000c07000c080d130040e25240c3e40c840064040206a00880003c100c0d0031040c01004d906101060060601056096091503440caa0300d6492401d03116825544014001200054140b54181c8081055890a4586800040070042c05070b46084492221000382c001160800640741d00c207940301005e10f00d03070b81e41030340e6144030703500000754080800350b9170601c1101042c0200e403005500543c081c610400c0404042407501084101d5500c010320450300ca0000c09008410750900103041000360a02407810016040c20100c2c6801c40d4422070300201d0440c09590003c40d04400184020010301381178031030030010385582d0555810182401d030740103400909800800c010715030354842e1810030f9 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 657847562 1250 657846312 657846317
    0x6050d1a030304030303090b0a0902061804060306051602010c050307021515030109260a0e0607030909020a02010c260628060e040b01020d050921032212030e10 70
    0x2000c601600081c070b5a082030b401140001d48401044c400c0250084601350010704119050045600b05d50004202c0c2c0a2054286d028522158003115a6034032038100c44000c5410980820841c1440024054100c5403011110003540c20040c6154016201d40304581c030038074280e03024007902d5000c2c000e05180e00030040d00071031594030040d2402c101c81d642841000ca903a072150980340600c4140c4001031030134094507484100010300600040d1000368010700407900c3e484003141e1591b69840f15140582d0f4a01c1c0350341100899902c0890300c0030740711340c05502101650700c0c0d54580e651051302c42c010b4160304280080d10004984180004111a410621031903601189a000700c401054000414107103044805d0b4460303c00a000da07540c1c540075080a2051801c1c0700000c0c07010b803087c1c0b0703625000136116208074000c3c0d03806900716890500040c00c600002e24070804c1a4003c0d681e84485180f40b02080f00c0a5090b4032034000440400002c0c0806424800d80206038541c440b80181100f04041004400250070750009 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 657848812 1250 657847562 657847601
    0x230301111306090602070e1501050d0614040f05040c06052506140a020c1518060a061e1805040c0504090308040b0a0606021b041e1b03050106050d 64
    0x1400340c0140040d041444041c1d80303a0401d14504a4000e050320100c3e03008200390740268400348400414444c826622680d940650802d413030014004a45503ca0101001c2c1e04501c0c121010401d0700d8400640740381104100c800340604103072942951300700c43d0203403401090184442c808000d0540900c000d0710079a401204258441c24001102c090b0f070340c9074410129044ca81e24126000310080002c000c90300300440b590210700348010010000d5941806050128081c41c0000020366038040150031408a01d00684c01e4a01e141482d00c041006461a405002c107030707080c90350240041200d010554070464070308002511030169298500d000806001d40b0598250018400200305501c40d03004844880f4803950300c441162515003480d0400c0e1001404007c86141040c43c1048a6540001d12030007200360106412060701403040060b00600005a8140303003481074050041804000343d0080d180c01c41d140544902e03150b04810100c04a03042406950702061081c414581c07200f03a1640f200340802140d00f42c3c550f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 657850062 1250 657848812 657848831
    0x20c0d11061b0a061b050706150b12010e0108010b0108071b1707050d0519051605010509030a02010608010209091914150a0e1e100b31230301 62
    0x105081c0c010000d582c0c95100c0b00f0000200005131256208103501c00310100032030750301e41400810601c101e0750043c00050300d4003078041c0f020b28901d075040003d02c080751806035070700b490600aa5004009119141d0035001c0d0b900002009581801000e5402d0016035511540d0f0782c43c80410b84130340031036030b402140c8010540a4000080c01c86041e4010360b01040504940724011860014902240402404200541030052000140318111034804680060400c1607c6e414480402c0e0768100340d40c000500158280418012506004001800130b041c040d4024000715440301c01083c00c9c0d116a184040c2c22203189000141c03c041000c82c40841041c29000100c0c807140e00d901c1038a0612000c0d9041d044c80e8516020b00314a614040c03015100400001c3c612460a1824440300c08012035101d90024150b42e00d000020340c81c0403a40c401c00e02811356440400d480e500c00001c9000003940b00c040c040320070042c2c006000380c0e2010414a60702281e141c06146400d40580f0480581010f528a4042c1d42544d201d030300b180c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 657851312 1250 657850062 657850087
    0x20607120e0111220f2105100501031502191218060b1c0206030c03090f0d08460e010f05090d0c030807051803030a11070501020c0d1106 60
    0x7040c82c5500c03d150561981480c100804100110540c03035440151800c0040241c5050130b18400c0845141140ca81120640c0560074041580d400c5c0b00200180280c18010213411070f03590009050740d0041c0c0841d40020320000c40704089100b550325101c0074089140c549840d00d07204640c000301501c036042010a01c810101315501210110180445482d078903180c11490606040b07681d014050001032a080c490075158010035000d20000c0c0585080240010000d90548400c0122203c3c42003123000710b42100f01d10f0031004086c0001900c846a2110f005000b2400101412000800b1410054145880c1d0501540c1b05d040000040c50703041451504e03800c01c2c8028480a10800741402d183c4100450907182c0b1204450421110722001da061001201c0f0040100360300141e015407226041c18000d607500015100003460084038407241e64980700000e44101c15542c091034001c00710134414111040c09803a0801aa2101001281d080c2c00040550840010446000d030302441c101e0007510b5a0314109a000b1803 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 657852562 1250 657851312 657851321
    0x2c06011d0f0622090c180b071106040806070f2c190b13080a2402090a0303020f0c0114070318080d0914090c0f090a2c1006020607120e01 60
    0x3c2c10319801141c1c4040001414600484803010313140d01e400003946002e2920701562112500a1281d0340d00080340c504208010500200c040c5c002c0100201d4581e95100409a503d2204403100c0300012044a03c214405002c0e0b5850140c2e140c2d04130389003601e0140980300f82002c420032070354564000881d403000307801e450030070711b410001c2c041c003010856494440c0c410034802c00c0040d0388901055401502044023150543c0c3e0260011640745034601c481284629600c00640900d18040b980700007024000010103400007500d0051081101c00d41305069544001902d94481d4032a0805035038000304203040004e0302c0340d18888000012107420070511501d8620080c509605054400e0102d2800002444510b1b50046900480e101c2220011382920f4403840c0c94030346003e14240b410194001054502490f960405c02c44080c06058a0345100280d44040c0402034000d01d5541c10381c1ca401c0300c00411280c01c407014100066941c107400800d02500c500c48120b50341a00c41300303e01c80d902e0b0346680400f0421000e004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 657853812 1250 657852562 657852607
    0x312061511010f180201110d08160c0b0c03040312050105030309100216120308150a060c24051509130b040c12030207060f0e030d03020d02042c06011d0f06 68
    0x30104c030410701d01c00501000c14030b000c2d03144240d0140c0c0300400e80d075034440189075100c900d241300c0c0c641c40c0075020b41c1500c0d64101a00d000b411140c4440030800c080c2c54800256204900aa64800b42886807008280454400b03004440d0150010052450242030540480340105980d01c126108102e1007a41f007982100e198110080c3c04034503940c100141a0720811254102010320344000301c40d1a41400070702c02180b944118000e00c4181001a014414102c0c0014820594186072080318003010302c1d20401080112989041c41030b01d00104052030500380d1865202d03050101c440e01000d0340c01d444003801100010021181a4086034000c10740000110028a05038841d8000b8580d017424207401610322420f8805540401c070305c0030807421260341d0000b220350426241d8240165101c5a034508440a40b1981d0050b03c060303075000480449075244d600d9040034a0b25400f0000c0d90b07603100c8000442e04070f01041e41d00c0344070400b0040e081080c0e1500504200c04807000070b00f110b1500c0301c9c103100c4c0c000303c442000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 657855062 1250 657853812 657853841
    0x4060209220614120c3601050a0f0806010302060d021303050604050705040504050616030b0604080c040c0201050112140a0f080d110a050409050c09060f070312061511010f 75
    0x1030b0308008200a1015020441c0e0b0100c83c407041d20408020141c1d541c1c0c1026044621031041182c060084c040031084065042d1b12280c00d01c50040502c05450b00b07130340701c00c2c41404c2c002d038014800041c602c0250045581034500040160040c0e03480c5808120064100e08000c68100d0307405c1200e08945200358010310020352140019142a2501d42452428400943e00c4580900e05000401c000110045880c030340c096140c20400c0c58142c4641022002032034400c1c170458122400103004542034200103040c04200c2c001700c609211016032400d049080c1d55013842001c81000c24088507200054011210080c0c50240380b00301c62104180751640d95070540540300940e0017120014661a80d91100c0c060145015060003500d843d10300292030043c4507105a204001c0710076038450102c1c0103e00300394200d64034100000d01c400d40310b20000840c81400d40c00f83e01d0440104480035010511300240d0300550f411a001ca55403440c844201c5076042d5070b6440200440409950b8410b100d1000c00d40c00d01c01c0301c00013032284 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 657856312 1250 657855062 657855071
    0x18090108070f0803091f09080613020901330e060a030501170a11010c03020f03040303051b060705120a0207020d12020114090a1101120e210703080406020922 69
    0x2445440300c0c10015046483c4075007041007a6042030b01d030912099141321241281c503280d034011740403c580c1d0103c59084512a806080184010305000e040d56000340c40c02110b84451a036a03d829140114032800c15560580d020050300007000407003040d82040703203960740c00d010700c6240e2a0750014250354098080c1c280881da44000500604002c582c6801601e9002c10040140403419110030004100c0c4124140c1040035180000c410144284034604c00b540d10b1034120b0b42c5403030300c1e07203006803c43c1c204182803a0000002007a20300c8201e4005030aa01030740140d2152031400120014200da40c0c0300080030007844075000c10140c0d0050304e9403241c41d4a018025208081c0c00d48455500901b52550608100b1522001900340041c030311001c1246070701d0b0341e031003802e071004107410074010b89401108040b1010050b05e4000e000402c42d4021504101c40088286a05802d071082c04001150b8012240d0141c00901d8080002d0000350b402e07401400c00c81b10080c02171407060100360712a07040140000340d0310303e60764a5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 657857562 1250 657856312 657856319
    0xf0a030504060c020c15030c0f27010f17040c080f0a0b091501090207030e09090609070b0f030f0c1606060e01090e030a0e06160516081f021809010807 66
    0x1900c1000d51001d0581301528948040b9030004280e207036407515500490301c00002080c11580c0c840d0490b802c0280513843c40d074641c22010210540b490301d462a004404500100700407141d8800c2188402d040250340310a000c8a00104078071450707100081c0112803100d04410701003454036042007408003040031a4010525600c00346408039000d407026012000f542d1051200000101c0644100c90544140d01001038403021241002c80700250142e01d03264000102005001540030b02141c6244584400340c00c44e03c0341903544a24000c50712850440b07401d200010700c00f051a0442120810383c1062140b0b80203401d01c58140180e004052032000704840d5240d03969400c000015141e480071b8010001c4c54000c0201040c04205c1c59101e116800000c1e00300291006c0c44c0e45641c0d01c1006990001e08042c2540100c10b8003450310540d16a803403524085500b607900c4000486400010f1441c2010384905641103906400318115000b80d0000e003490104142c0c0100c200000341c8648011074002c002040003004170310316 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 657858812 1250 657857562 657857573
    0x1508241509100e0604051207030c0b18030a1505091e010e19170a03090b04080301140907021c050d090b01180603020a180f0617010f090b04170f0a030504 67
    0x100c0ca403404103005000d064514244d584205443c201c4006940c202c01c070a0381c0050311400c15000342c0004080744403040c0040b076100c0b13920000d0001450800000070711852440105a13660030021002070542200140210086c4026003211b03030030500c2d18048400404420003202c01d05e21034032040c50003580d541c40d500c40c00c01c841040621340c003150001304007030b20602d25125000188000c2d0b1450041100008015070320601c03a03401803204507080344500c040350401c0c3c904050310360f1081c0b141c05141241c000e1002420700c3d22a41c00d0380101311030740041003080200c0c01500d8540c041071640c01c061020500c00c1a030014240c1c06808002c9104110441340c035030404503c1984094000d091200d6185000c8080c0010784a80505105451100c41d0380d1000008010144015080301c0c0c500c0c08285080c00d000107841c540400381002603440382c0c0000e009824401c07040000700c1d090440c010340018407035808200030030015640400d01d280d0000580b07203019038034112150035511034034012001a40d9001040144032 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 657860062 1250 657858812 657858829
    0x90b0702030a1d030a0b1e01060f09050402031e090307021e03060c0f07060b120a030305010510051305060f0705060f071403190c050922061508241509 66
    0x30000403c204507030a1140401da443c40400070040c500a00c01020035070300301240707080c20341c051030b90048440780350307110b1000500302c0510204003004200307506c0020500346424001c2d00d21a0b416900715a01c903c1c020071402006590103030209000380000c203c0c1501585401d024007007040002000a00c0b0084c820042c1490300c50010101d03801480180903440d607240301071040300c020070b4026030041000030f40540040e4400c520070b50001031510840d800c1100f01501500007074101c400417180c800d02c410b4031050641d034503c0b0308000c1d04a01d041d841e40600081c50b041028045108900000d14140005507a8a40c54600700361000314244a40c2d900300301045902102d1400300500c0b0340c00a41c1903042030340b0a45c0a071440703031b040840201d4440301011005803041c815160003900081295140c8007421100c04440d0f4030030349030030794003904094010641141000f412a640f072102ea403050300503034461000401d0307205051290380d03200000e1285411660386060181c9094181031440550391407a0004106c0c030003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 657861312 1250 657860062 657860087
    0x180909060b0901090e1c1b0318090c05040501030906090215030103050c03011b030902031005270109020109120620041d0f0115140c0304051c02030705060904090b0702030a 75
    0x15814007178500c0c44e403500490b07400c224104001101100b00c0220b00103030703691f142c2003408403080c01040840d44240f5a02c642d081d40c01c004107608021200ba110f2807580140d8900c0b201c0f00c4c01154003000104a10b51003503000e035605500602000842e2011940081c10a803100041d01c4154031020005205000c1c0c00d0101c03081e00c0c0c404a000704500e014044511904070344400b40b101c00d043e6102d81841c1552001d1000b0b4101c1c2c044208200101d02d00341980391503104440006244d01e00c41f100d07a03440340d032805100300049203405840b0742080ca864041c680d407412031610b400b180c4071522600c1211301c0030640504145000d10716680f03d80c0300e070b042c08040e00c00c041140324a0703147d502c803042c1800340140b600708601341500c549445c0303c1404036244401780c45041c02d09918001ca40d50010b0400112400840500261013088650b001c4400100b035000c0e401030000d03403010b540364114010800003072074458002c10000c00054008100103590f52559414614202c550b40c02681000031a440348030741c440d8480381070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 657862562 1250 657861312 657861329
    0x512010e0132012111040c09080d02160308032a040306050c122205070e271207110303071a0c0a0503010308280210060603110a180909060b0901 63
    0x203c1d07140940340e1a86403c9010300c00191080b02400205000c845254200242d0025001744411040740300e009010b08014030810100380203114103040c0082c0702085444000d000203505408003800d542f11030503250f001030300710315014244ca049403a00240c01503040c1c081c500b540c10b10a484501d58182441981c4000349604540070081006001ba0b40d690a41c841e044901e0404052040c0f500801d4481d4910004c00b001d0401c0c4903000c800106c81801050051258955260f0100030324000da0750505c1000c2400d5612489400240300140600110000b80600c140651450050b82e0500c03004241103034410340058400d94000c105840c03001d0410054142c00c01c107961281458507c0f41031000386103003c103000c0104100b10000f00c1951b0340d001c0d9646040c401d00d800d51b003a044024841c0b40a5640d2600100f60b400d494246600095050700a110b9401070350070041c64145804c04000040301c541c080b60400159039000c40d40040380441107880780c2aa4588189400101142d03480100aa0341805034840c400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 657863812 1250 657862562 657862661
    0x204080601090221061504030602091002011b0f05040f060e011e020c0913020406240810030f0203120d02090a0803160201051e07030e010e09060603010512010e01 71
    0x5480005009210480b407506a8241d064562a00080382c041d0f541b0505000e0000220780403050000945c010300715090111b81da4240180720078020b90036990b0b06c2d81d0400c0480302120403860f0050184440e001c00c0e00715850800d141a85850301e4400b040d00c0381c2c00c250005000341411100558000313150244840381164100100e2410710350003950f4a8003040018000d145602c0451703403045090f080001d805900070820b006490b103805494207100c103050030000c1030810f400910302425000d40c2005004a02010031498018219181c0c51440c4241c400104c2e054481d81701100702481800700504003040500f4000742c0c1d5014540100036044101d03803c015001e8104000700076190240c241c400000701c3d03083c00c1881d10b8809d0b4070100006e00d4901c2d00c00e40e000c0700f400900801007540c000600268100300362903140c0c0d107824030020f2214440c4200c408940005042006004c20720f41000340324502a140400852184034210318142500c4008aa20341d80030410300c80100411907443d0002d45421180a4841 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 657865062 1250 657863812 657863827
    0x6040509072301020a0c080a150b030a02150c0109060b0312040b09120a0506040b010303140c0d110102160503071202151603020d02030f0a1a010203030a05071e0302040806010902 78
    0x401030040003281c20710840c0c02c411201050f4002d00c11050410303001000c0c0c413040b81c2e03140c19041c0c503644405412201846001c407005064040703840351100041c405401410703c19059401d000c00c1d45c000e46030619560700c00f40100d9480c41000d004510030f4a02c2860045800e50314072051620742a15103e0f00c000c04c400620051200b030410100792444584101e4400c10250008004242403402d0440b000d0610b0280e80204014010742c1040d1034101e80c46552606501a400c918000c0c00c4d01801e02d2600d801c0d04501d0b8030310710640c8100d480c440140c3c50300000514150203080c641004401d4484c0403640c0c6e42001c18a90103010b204284540c8010890000d002c5d005400d03041d100e038200d00204859000150382d980e2128451103581610b40311509060110340e03a0420b94414855a20308a07607d41c441d03410714080d14010024000041030186042c2c0045043d07803181829800900ba00800010420400b0354040000181056052a41054945005903030701d080c00311860503e0320503004404010b00410069 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 657866312 1250 657865062 657865079
    0x631051203090f1c020d060c0212070302100b1215090111041a0f120f0a06060e0d021309121701090b0d0b040302071a0d180201052505010f02030604050907 68
    0x420115004076940715465603040c0500900f1100413a019401410b2030807141e082020a034003024802d41c60b40c00f00c80c0c0e04075441540500a2294140040040e001782d0118965003640360040c0700c0031071000b02400c00b00c8034001412841c211100d002c3c00d442c1210034040c002d481d0000e100e1030714103424000c80a4030300f508000000d1a0300c40040940c400d030500c00680d00f441c42442005031030703400f680c0c0c10700707160617050011820712800002e542d402d00c00c602d49200061148e01501d0b10511f000000713007001000140503001c014038a4140c8a44200144d141c440c41c40004100d4888842d0401580e141c401c40403078107040b401e007403c8058016150246c5080c4e0601d0080d500c9201c51101c3c907501203983c11844da1f840c85c04905104d210f6120203050342c003081c220301d030985c81980600060078000c00b081000c403260000e00084400d2211010780443c00400450b51b403010640244898001c917190342c07005241540d91000d00f12180c2c1651400529070110511513603207480d0140c550004241c800800d401820003c00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 657867562 1250 657866312 657866329
    0x12072604050108130b07110625030c030603060c02012c0304030b040201030209031501090f0506060904020c0a080d0504120c111311271e063105120309 66
    0x2070724103120081000035030014010b5401d54029902424810303150400400203054030300070b080c003901140a07440c001801c3c3c0804c8480300d00203542080d20071f10740c100c80183c20380081849200078400c16440d1117020000ca00c290144000d40e034810742c00001c0200d01d402c40d04c200d1810140007400550203648030784407404800001c0e070381542e4102c056007849803982e1006030000d108103070495405008403075100602d281c90720061030481d034088009215007400041d41a04a607421525103501850034081d00c40d05042a5015042c0d4034440c2c1c044a400c00465200c6142c0e41e042a02881551600ca0081200f000460303c02c07840710708210f05042c101c1240c603581f20340080d65400b840c140100032807281000c0381c503800d4100a5040354400d400c16901d003140c21181c2220a01c0c010350940c004170f29035119101d800d15214000940801c00780301c65110121004101441d401200c00b0803d0f004c110100c00701454503440040c00d448460a54010103521b0141417081e07502c0b031460414115041800728480d20344500ca003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 657868812 1250 657867562 657867569
    0x6010f0e01140c010e0706030e010603050a23030301230108010506070b0406020906040e09011d06010623030c0a090509060f0d022803031419120e12072604 68
    0x2000c000c100b030014240152400b552081c0c00e0550300705001e09082000118075201501d0071030750240b050840c1c1c0e4561500b238520512005089070300c140103880c0400d0030351710700054601e83c1c140451181c2c40000034051641c3c000b80c011400c080d000030f90a240b100d1400d581200d1416003800e0543e440d625003130018140c0c2c000c40101030a080c004e0400a400c100307141c0e0444500b85001804103482d16240c050648075860f044410005940c644029141100c43e102d4401400800710720051a943c1e007044001c40d00c0101e4480c29880d040ca0060786584440400c0740a11700c10000015016260002444024005145540b11a00416843c01840820748940200100618003950524011032252010428114102003080714070b0300090304406203403a0001e001b6080b82d00a54442012400605038072480b40314809c4256441c548600c840c110b035030300032440b1004459054000144d013069080840b41860b0359040c03040001034002481a082120b04104900701915500d001c0021882507507420741184551700 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 657870062 1250 657868812 657868817
    0xd0f0906030c020a120302070c080606210705150c10050702100902010c06050112170c06071b14070609140f061c061202010807030b0904060b03030409050405060f06010f0e01 76
    0x810542140c3c1c0200141d03541668445ca6840b400740300c42200030000e42120104a40503615940300150360b820000348203009034030081c110745e59122030704400c22010384641c0c0150000d0082a4000685075a80707142c0d0581a12854242c40d95511110501410f2108146900000f9447c1409020300c1c0c1ea030018085100c500b1040c000580c050b5980010707101c0341d007600c01c001c1240f4281800401c01c80c0104009440362172148210140d490b5542d02d10700040c2c000e6003241469a0300c03050000d10322905c14080d1004200c1c842d46e110804038844d845107030340342509142c0704085600c905410410076510000320401084d0300070725003000642000c005500b4203041c1c41294032407400413905040c07801070381c0f241b0320303228500715010000035a4501d000790751690b81003001d0b400300c0d880c080004d002c0d1b40640034850103c4070041840b41c2d607aa40307139682401803814058554243c841400b01142810381031203102d0080d03003d00014482480c00804241c5291401081c040c10030900c62250202c0039084103a0003a0000c090 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 657871312 1250 657870062 657870071
    0x41709040608060c070317150d06180b040201180b030105060304060b0d1104060b03190e1e060a0506030c0102030d0e0309040204030b0703050f0123120a03110d0f090603 74
    0x900004029144680180d0001d000f1a024008112030300c400030000144261a05103114044440c409011a8200d54520400c20822654a075600e0800c10301c0b0070842c8140e42c00500441c010742c44c50f00c0d901d070b01b0004490740081c140911041d0b6800075483c00c06588c400c00c84001c3e150419403840340c00d00043c459980900380100125080007050713040850202800790851f2070301812420f21074400c03458001eaa5000c1d40c81d24601203040c04c0d0030421240714400244050540780c02660b0450000d04590700810300c1409003c04140340c0d200c3c01c50552014807420307002480c080c10f1065101048660143c0f0301c51180d030000c01000d05598011080e50410320303481c900000c500b41c500c45c840e42035100d4800901c1d84148005008000c0281e066031450044086070b600b04802e03034642080c88080f030300a015451002c055148014440e250042d4540b000b54000b900c4100480140d071141490503218400460100720440143c2c10020300030040071541c04d00520300700b11a1051490301501c2d510343c078001c0700b0816494 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 657872562 1250 657871312 657871327
    0x90c021e0615040f02090d0503120106030b010f180803031f170d1b080a03050a050906010302030c0409022803140a030504050d08070c0620010209181b0706050f0f0417 73
    0x140d0305852186e80003070001410b22003280340154490380319480c8054822128030020840350300ca4400c001c2c6481c010b854800021401400549510341d2050310340e2854008150041030038401800910300556011107a41169030249800d40000030160700711603e60510105403449685d0009280c640c09003050030704401c10004210104068080010058200000047c00c0c49030b1a6240e40410b2040600d20340410498036030302c0103151101801c0c40041c3d0300d0b070701c00030080c0c80380d00d4076500c0f81004500c0201822150b030a41c0c40b82b000c095042d0350780e0320b226110781c600030000e0001c1c01c1106004248000007610354511039540283c800e0266000385401007072080e12070b0f0f04100b981400c8030120f036042541c49820fa42e588000800c0f052050303208414413221411041014030381402555000c4a0041243c003a0079040703201801100310007000301c1020440c00d000b4030140c404640090074031502400c00410749180103c030820402001801140071480352004120100c0c0500390343c0d0701e106003991007040d900c400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 657873812 1250 657872562 657872591
    0x190309020a090504050307060b0f0f090a0f0603051522080901030204081c2003180a03020d05010c030c0914090402060f04060804110d1a10090c021e061504 68
    0x20035400050442d4034182c24001400400000380091138424402445020000d5003800b0300a4214882e03a900210241242182c5180101d500b55000d41c2d003003400580241c181b040070054407090340c02074882d07401c144040340324403032120100759001031000e4030030750402006c592258850754441c1e009490782201290000090703102c2c0d01118010109441201c0e40300c081c42c070010030203004101100020854514640b80712580180f5000c0c0d444114030b0180d401c0180c119107100b010034004c40c60550003402405c003c40180c1e40e001580c040c0030301580000601c140304860180459400654000a000c0805010400b210f8012007542d01c51401b81c9010300da031345851020600d18004e4034034a0f20318002c081400305003035620001d210700c9076004d059442d503108040d00900a9030341000c14090200c201a004224001a000341d05a40022041e110700e420203036620725410484400c0c1c003003040180c1000414403503000e211030020740c444891034040d0406092055180c0071190517600031078022030b2038810340c0602d42c2 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 657875062 1250 657873812 657873829
    0x605180a0311070e0f0a0b0f0609063f01060305060a1401023417070509070207050a030606080c030f0d0c0c0b1b06091c0c02240a02010605040219030902 67
    0xf042054804a00741340e410f011500702c1c00c64910790703c5403a04041204e10300d411a014600c1c000c000d001c2c1d9203058000f00c28005a5840007042004011404cd01c4001da00201c1e40c00180700c3c1002c00c140f88100c1c0080001050310981a0b21010415080c50244061030f5503c03000c160444020440512045041000603030a01019081d41e141c50641440114900c03000d5010b00803400743c9490f041c4151680381d0301c2610302d0b80c100860b14400d40c0d010500510450915000ca035402052030300481c0c01107035883c00003460750340454008440315a03c0e20300c10801c2440030411101d08420480240100d400c0641d9055500e001260210040001118a9405200d80400128081d11302003242c0303a038407072000c66440314601044003015424032840000480c0d0f28804a9080c810715414595400d018520a004861442ca0042c0907a40014801d180180450415058080c0320b484120740301d440b681c0580c030280c03c480c0e650b40300c1ea002c1c50041181c500400120354203e00d250615040025040b001400407440380e0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 657876312 1250 657875062 657875069
    0xc14030c010825320409020714120409180506070e0f06040905010620150a0f1415010203070309090f110c06060f060901121d011401030605180a031107 66
    0x22100c00d10b0754103605030301c0541d0b291030b0f45100f1190340030390b2071040c4c168842000b914a002c3d0500401e001c18005030100e50010064a4081c07400072501c100c0e11114035051403822000c02902c010001020082c120f480d006401402103007280300e0a061039540c940980300c0030014400d40410019458282c030580d12001d600604079005844030b030310340740c407684104000e16080c041c001c0813600d6a940d02c2c0740422003a04c400300002a0034050000c040c1c0841c480700141d58060481a145034480303501c00c4ca00600c030b21a404d420000d5010b80000c03030070980d402c01074a060001001c3c0c11904108181800b1075088404981100c8107200000340700202104000010b24200f00b41200440e000290010480310008441c0e01509046854442074680c0070b041142c54410390000d140032030504202da0f415603034540c1c081c200c20102215200c6100650840c00e03401c40f4030041401006c440042c005209015a91041503801a544c540a41300c021080d0142075a90780c98000082c02c0015485c4c1c4504012010b00c644c4009 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 657877562 1250 657876312 657876361
    0x51207090f0905012117180904050102030610020c010207051e09070f110a171309060914160801170703150b01030c080705250f08070c14030c0108 64
    0x3030b0748642c0e041019000a206002588812018100703000096000c401500759208012100c070200b200c5081030940c00070040ba504c00b108658852016449045074280b06a01c81d0000503564a002030401401100c10140001158080b4a8114203070341c00060441c140c0b04100c40f0507c00c00d0160240482d03035185070a6140d04800344805108910340c210002401c541c4440c0c4510582d090854100b654650903020003801c40548040b2404220141000400c521a000d4903039030001c544419040041d00c1190b400100e0f1745a66117181000b004440707030782e19000400d030b00480f000c2c50b01c0c4550042c8800e80601655060b818a44180c3c0417040702040f401c0001e41e400081c40c10b8000300020aa0000c102e0481c070140824242141803042c2442807040c1c510464607070312404e00302001070303185d4010524040781c281c4069402980c1d0034045409444040d04843c8121580e580e24607042c80e00e0003607000c03164007564040b4611141101182e0740864102d040c1c2e40d00786082c02081d6540781c040000d14030f050402040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 657878812 1250 657877562 657877589
    0x50c1606091403030106020613051f0213030503030714090904060e0307151b0c0b1602010b06031504150f0e04082a060903040b0412050304230a140105120709 69
    0x40b59407011000d0340c12034909800b600c026598003901c40d0466803100000402c9034101c0110204c007004007440bc0008c064030058014244820900102c841c0c80745a041550300d94008401c05c0421603002102c6081c1400c1c0e504400d0801d00b41101042c80e200c3e010300028019510ba40004044810820a40309125040003811361480310700090480105100524820b09041027043c0c0200540500000c4031030341e6006204841c0e0740e03102000c442c854181420702204554907410403054a6480c04040d6000d01000002c0c40081510f2200704411900120780000c9508005802004080036034451481147c034a541c2102c010303925480d02a00c00c1c441d0310122110fa1100d03031b600c0751460b00c00619101841501c20b0450f4160f031603030300c46280d5070700440c0f0039001d00c1c00040006020004040712803c0000d8454400c49040680b29025042101048421201d501400004030f000a240004580c0c0c01445c983c010380b00002902c100090140c820860f4101d681c9981002003120300b441290b92000500101d01080c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 657880062 1250 657878812 657878843
    0x20312031006120912080c1902070e07181503020706180b06240c030c03030f190908180a090e032a0309090c090a061e03050c160609 58
    0x41901c1401c0c020703040028110012880c03160a00c1c400c80d00344c290400100c4a40d40201c2d04111183d0a005110026006040c00201440321403402c0c41100083c9540140403e2820701e40e00c0300000d20014100001c0154103058411a80384000e00002992411074011600410102c810380182c4034140005020f1840d0040c201700c003500c0c0d44100d4805074441c640400140d1141d01c00c02851688454002d070303100e001403240b001c0810100380103002d101001d40640342044421103201e401c58000f1140c8004264000b010080d40c003502c0c4141c00b40c42d4041744810442141c2c0c03911005c540b4064400e10040890a000d6818250b5803201c1d4220010308041c20300f4044c911003551100d0b01c0350403031880e48900c16a0090507954242181c00e2800401c0d094900031410560984204842050041c00007000700000700203600c0951a1034007502d0261940d0b844054009620651144c07505004500d03c00405203000140710185a0a8040b80c0210801340350140c0c02014034245040181f4000c00000c1404c0c00051102 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 657881312 1250 657880062 657880081
    0x9030203030711270106110f25060311041502010b0a0602011a0a03022b0f0317010b18010e060d02131d15090424060e0703020c100902031203 62
    0x107805503001902c850b92054800c40203001406180200070440400704e03001031000e00d1207000364841c241c0b8140129510101211240360906d040300900000c1e062100c2920700403443c40d142d044004040c1840e00b0030012500001c0124580124090f140d0701d04c00c28500c0030a80e500c01d40001211001c003c10424a0644e5044080d0080101000d03c18449021803401c0c0340701e213415401c0e141200d070058081c44041c010301d03900e40800003016108000810010400e000854507000303650708014400e480e5083c008405502403800c071201613003d00d14120b020058810809403c8150f40700b02c05080c200500f045184400050b6140545440c1100780c038070100d0800030408034240c0d0303035044860351044400c540000903002030070400111100a07030b0348900d4401d1a44c40c00c0900c0c00683c09402800001c1c501c41c20038048046180b101422025130a131a600c040c8103290f00d801c2c456030803100c42d00b011458260f041c000540c9910402d0703005028555600312a4055483c18803080c401d104518102c0e80c0d580c034040a10 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 657882562 1250 657881312 657881333
    0x3060e0d030b1e091b070803060102190230120403110f0904110607021005070302010b04180f0c05040c0c060606170609040f05030309150f0f0115090302030307 70
    0xc0100090400d4407102081c2440410841a020510740741403500950b1003c0c000c4c9000050f00a04416070a07040c80d030502c108000240072420b201d0913086941c0e04044d0300091410420300c5821488180800880005a4824501110704003008560185104603852249000002512251854080c8500e040060103900006005036881204400089050340050000c1c0704404c6451542102c5030a001c00c0204041d030107400d11204005200c070b0700e003851640c041016000d03001174280c00300c0d8002c2030100c100342e020f0051041d00401075404020f48c1c4a014406400c4221900000d003500c60300f0449801480360701c803a50005410050400e0209003685a0010a80f84070b15505072501c519000020a00501c29509072001e01c40794552504180c42e06070070031501a0018104483c0702040b03c104000095090000c1d61107003003c038014218143e4119221000b882000740b083c40c1c8050344038208055140074410680c150742500c1c030a0200380d042484181c51200180d00065814440801d640042041090700d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 657883812 1250 657882562 657882583
    0x30c0605070c1406070e0910051008010302040b030a050706030b0a0906030c030210020106050609040209060c070b0d0c0903020d0609020d0807080d060905060f0603100e04050a0203060c0307020a0f0201050403060e 93
    0x81d403e01640c80c040c588a603402e4804000088a01417040e4240c5800a44a0780190300410040c1610f0350714400900010030121000d804160300e580104190324003446520500c0c4000da000d0b24122205964039078940d0786074003900c0305241e5140c8d01a00709443e030018200c09098001420840340e6101e0800c3d0103502c0042c48228442c11180c52044021441070242c0802c588024000f5800d216000f4100070294014440c1d494101500f0301140e001c0300420884074000302228100e03180d40c0d01c4071b0300b01541030b603a60f4843c40c41031220002c41000140c0b00e0b41c040050b102e81003507000070b041c0c155100240150b00a14805800fa42c00424070506104202c4001e00c2d200031541c3c001c004113952506400181c0c5d03030440d0f03900c0e44403603c10011319090400d44010365014011a4a2805d0192a0314005401c003106035000d4406034806800ad5046080400010350040415002c1074114034245d98000c1d5250b030b0305c03070f801011a141c9082c5542164015015900515440a01031110500301e4541654403242d140 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 657885062 1250 657883812 657883823
    0x408060901241d04030302121003151109060c010209030601031202060601080402030c090702030c12120718180b0d03170c130e1f0609030c1d040f030c0605070c 70
    0xd140c1d103074001d100000341154040700c140621a9283d004003440d03941d0080c01501410f40800c018081c281503004524400c2803804030b0441114190304114900c01081002c03e00e0b030f2450f000b1840131040c0c0c4003040d82c038414011214140da6050084941d40640514070407150948102000802001084110700d15442c01d03076070031203030f840d6529401100e0110701560080d41640080790708511b2814405d90380c0d60b0091290040701d1410092000140c80e1018008144020a501180440e1302030b405c58131442d0024420b1600b041d4418041c0441c40e200400b40c81815100004c00100b0001031101c0d03042000580c02c000c081e24204611414090000c104200e42c510030901c0c1d14000840b41001e44090b50b01c0d030608201c01106c02814000f001c0d40ca0039000d4104c1001260381c1a1026000d141e1130020400303030015070350b4106054590701d40141d40d6011508207021107581030308944080702912850540c000d0300516001c90711031060805480c80400c0c000050b01090030002000f01e441d0b0080d014030120361248 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 657886312 1250 657885062 657885101
    0x20303010b180a0b122d040803040201170106090302011404050916090e070c1103010507050901050d0b0619110f19060b152a0a020910240f02030909060402030c0408060901 75
    0x4d106c41c0a00c0420345000035007842e000704001c6045032010f141d000d481030400c90f507081d80b0501400c84104090f44140006482c0e11014000c40d40d01500d488501021680c9040c2051304100015024900c0101000009a04400409002445002e00c5001485600c1c1c0315055803d05401c010542e06c039002e401d071824030900c00900d00f281014441e141c0314401d540d982d5814440b44100458807039010180c9609005c0e114900e1071000da580d4001403544000300410350b000169000405000c90b4241c50b0001c0f40e45c0c000c1e4101c580c07580800300c0c20000c1ca10f81c0100c0050222076910340a40140303480f00c500c40c1c2003111340500e1540c0c50412070040146000795030504403007112182c550030940f100c1d0118604680c000d84009001410103c1d005030300030324040407034040b1a8564480a00950802d000c00f01c8d0040556100e40c0c00a0700825402038420845c4040c500c3c000c074081c0820700294018100c0b5010f03540c004000b0315902c4150003030758040c3c048030003981c401d824911038070f0f4080c160b021044500308214 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 657887562 1250 657886312 657886351
    0x120a120315061d010509121009021c0506190f0203091510050109033e10080603032212030e030c0a05030d0503042102060f07020303010b180a0b12 64
    0xd1810041800083c0d40c1e811074103a000c401140c054204519460301312941d046180082c0005002201c0031440d107803400544002c0c3c900400c82000302540000c03228804801250011400100e15207a00c1200051083d80540c02410000024101b024000085078030201c148151090f0208111007901480d915210682e16494004514050644162070101d030202d04104000307500d50500c0003000d000e1608410400b0450410006130007486560304007a0340c0d1041c02d290407494482c401361805c1d403c92400d5003036403415401003a9039110f0440780c103005e68040d100c0749400c180c20b550340b03030013500c1106420f02c806c0c1c61a01d40a040c03503540008071482801040d0000c0418104020a003003102c0000700148040031800406031510780c030262003610a84480140ea80c440300b41003080c004000095801040e40303140144c071202d0000e5000e0402c1007190000c0004001900c1d600003034400b200a41a0115400240c2000003020050703e9804060701d0341001c5403610008441c0032000d4440d800e044d140d80e9940d8038 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 657888812 1250 657887562 657887567
    0x3010e04080403141c08101403010b030304030807050105070e011b14030c0a03120c09030209100f030c0608061f03110d0f0203070216061e17090c030c0301051005120a12031506 77
    0x8850f00c0940300610b0004100d0050180300600c230481000c0c0001418034202e601090540d48280c0003a28000340000c0e404080040900c01c1540c05180d44c41d02d6029604020002008484032402d03c580b1110301661800500c441e00c1c0c0d407a04081850004c8940d10044a000c1c0c60b1550030440d800d902048104d86c1c003407250b0300640a92070b803401441c1d4600c8005402e5908100c15420050a014001c044000c0301107004061524424080c50044030721012161400000a0400000900090051082c10040c042c0a4000301640059500d90708005c0345d582c1e80700c60005a0b5010ba8800074581a0070166544500354aa500035401880103900752003000e1410764580c9100f0002d449030400007104804130140c0350018500700c1410180f5490400c0303411000b902a004a5441942d031410750344c01850000215290030400103020540640081c403481c940046060074100072032040600880400c0420304043c0f6007481100c41c240d6104103000400c070075004000300107110900760340702c5c100d03028036010408a0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 657890062 1250 657888812 657888827
    0x50c161410090806010b070c0803041d0a020a080c0a2109050f0f1f060902130f0906030213020304030309020d0501060f0506190c0606050307061206050f010503010e04080403141c 78
    0x80d09500200070340d074a0031b801041250b03c1303080c00380c40400001ea00454000d109000400c01003204041500420a0720391019403004005082c0751081c5104010000d0703850b8000015a40c04810b10070305a840b0590500141d41c8034108680c20100c0001079464401500c100703601042034540500100c54941c41914607481c0e403040c0000c4420480e5100e500000c84003038818924007003204200c5008100c5035915004801a85c20000541d0000c0d900104140640d1035031058283c014106070f282400007505c3c6030042070035600303540c080c2544950000001010705000f41c0019440b254090203c01518403103043c003900814040c01040402c213209080002c00d0f2804205032400000c1c0c100c0900c1301c40d4a1043c1c01d607018100080100c5549860310000959503030180011307001441c1d82d40342c00da180c0e041840140203c5019800c060701c1a42d41c07485003101a41d00c4015a4191840c3c2d000c600c000e502c0d00d06081447c0c0c0555840100b05520045140c1884000850f003c030804144150401c0e0110140720140c0c0e412 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 657891312 1250 657890062 657890069
    0x9040c030e210d02160206070b070e030303010b040608060a0e0103200414220b1806010b040806040209071e05070b1003021509010c171c0c020a03050c16141009 70
    0x30002882210f0340e00d22903500402680b8500340e1519900ca00a03404100300380c0140304203545205002007004800d5421000480c2c241c001107000c2d61a560400251510394007850040310100180b6074009012134440c820101c0c06496400700320001c9603903030f18041303024106804404a29903d00c0141c48500d050a019183c8002c0116505a80d07582e02e85810300d00b10369a01040301111031281c1200008110309410040c0208003e140c0c82100c2040c100c122481c100741a0b1002c04640c8040104003c040004070301180c10550460f07008a0a0721100b008031030740300060321920503161000c050b07a00b04503006801400c0d0075206141c040d01a568500343d81c614095a4400a9045540d0040307400c02d0410010041c02000014100411a14802d03110f40420390304c2802c124154040009440041d41118400640100300c400410320140007186002034480f2960000281403040200f0486070102c418043c9601d5039092041c03d9200c2a610400c448852a0101c074181c084c0501051b03088541c3e21030715090060303 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 657892562 1250 657891312 657891373
    0x70902030a0650041b09060203090607080a0507080c0c09060414150d3c080a030c12021c20040e070302040806010f05030706110d0e0609040c030e 64
    0x315410f52446108681400840d0b08948580714a41c02c2030b40c45100b00041c0820150296116442c8980040c0a00030b0340e400060542d4002e00184407103941321422141c107180d002e44840d865000504003603406d401141002800000d000c22415100800001c1c0c128100c9806c44880b480e070384403070007400100c400c00095403490701d9046000444910321b18038441c3c1080c1c0040d00c40304440041c1e85403409285201d0000c00c01c0314141c4406c44155000e02840003030301d00380142c4248030140043d03482110503ca8002640145078a40e0502c1c141c0d640035243c84288a140303104259511110810341e03058404250058091152800d20071455011900c06000100d0115850303142c03629080806913004100014444020103800704400314081506000d81c03402040c01416014646080008260070314285411038810421410140001d0740c00000d81d039488080b80e410042807514003e000700310184900941a50803d05101c2d8460100d60f05a0021112748a520241d8a182003803810340c00346044412075417180b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 657893812 1250 657892562 657892649
    0xa020f01060f03020d12141206030f03030c12040f0b010e09011b1b0602160b01090e010c0f08091006080a0302010f09081b01060306090803061207060818070902030a06 73
    0x161850342c072041d0b034116070030480d5403003102d082c90034071951207040d50201010b208c000f40181070a040100350036020038103003c1c40c01c615240100d001e6500524003107160180c80ba40124003070140f80c2241c801e1280c0c12446440391076840b111856440c980070790740928607601e0030513500c1d914900ca6040002800c11581d42c02a00040b410b02c1c2c05614520340000e54503607a08000f00c101145a078410811400d00c141d003407000a6242080c0d9400300c0346a01007001513641031280803010303540c1c031240d5490101c201e828031480c0394940340c20b4103244c1407902c400c50304481c3c0303030580102e0086c00014410f46090320a60007444032845c1c0624060660b0005100105554018444100716190400524000705415400090000e0762070b1120404d4580d4440c0c12b46550100000380289401c00440e450310aa02c400c00505402e45000c1c1d004042c01c1e40100449036002c404400d03448041024051000204260300e41951241445d0300746600070607131881103076100c10701c0000c0e270081c060250460041ca00c4040c50f0609 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 657895062 1250 657893812 657893839
    0xd0c0f0c0209010b0c0309030a03090501171003060c12090b100b04141c0618110405090a0212030409060e0a0e0d0e04020f07081318090215070c08030a020f01060f0302 73
    0x145542c00c0740c000880e45d40020300001d001901e040000f1080540281c0e01c02020900d442e0015124030b024140340c0c144074461404100d03d1851044810007243e601110008445c5402c41e01240d008100a25a60f031007402c200c44a024407941450341d03400359280d24144d5922543c0c80c80c5031040c074405c03482a000c05116038095003410703241c41c03080c0e08039401c0c0c1c612045510392401d55a400864605090715105841000030703030001e020748c2440400303525205640c200001e080050500e40e562545010081c0300d0031054518900c0d506043c030640700284100b0000f0300003107480f92814135001008603a041c40c00d519000948240a8000030707442508001d5459403500e20200da0280806540701d0780000700345e040100001c0c0000b0310703064020100d105110914094042c2014000102038071142e040b034034034a003041c0451016a8034603980c00e0350301c0425008140c2d0f61030286445d001c0c290055014002900010a2111000f50046250704190f00140000c0182585490344460840b0450002940040075201010b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 657896312 1250 657895062 657895079
    0x605070201091a070b0a0c02010f0608030d0b04020c010f0603050c0a150f21091103061006080406110301080604050601080627010b060315183303030d0c0f0c020901 72
    0x200200b8a810b8042e40381000395210400317102816a9211040b65562441000703150382032149041c01d080816083c44041d14040010740e0700e015484406041c03a54400703121419580b07da040380c07031800c18000280b20240c0d504128a0042c4800c0c44161064000c41051031110314040350040241c50804400b040c46c104194001c80e80c100301a20204244101401006082449100d0f59081021031110208200c415480c00c01c245060207681c20340641c1c8801c0501c2140d0807545070700c00a544a030302e01000d482ea110309011010701a80101d01411460001c000700e0b00010204015204078090404c03100f00340d0b60b44c914140e880800701c0710340032032814801c6500c45903003496281c9455150380c0000031401806100001d041e0303600a54940d004403038040f01c40380c1d442c10404e084201c9520030350808103003840c295540310034050344885500c0510000088443c0da0400c4801c0380b152146001d81100d44a09400d5107000c010003092441c440801c000950346045580302d89801560650f025000c2c1460ba481c20b01203 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 657897562 1250 657896312 657896339
    0x40b030406140a24080c0f06070206030109060e010b12010b071b08032d0405150403050a08090a2306030901060b0c2b021507050d020711010801060507020109 69
    0x11100741d41c07998040520710005503251801011904070015101e16080d9001007913864680110104401404040203408404504030030441c81c113403130181700c0c4443d900000e0b1562150f80d50084d030280d0040300224541030355901c00b0094542c2c6043c01c442c4c44c5d80303c08102036103005e404038407080580e056005000080c1310384040c02e07105204000c0d0501d5555000011070b405a010b412412840d88082012401260001c01c4007900701890034403984001c940c10f113103030300610031800744c40d0080f46000303050300da401e055a04840080d5000f1098400c06015440d085605510003500b55101d041c2c00341d00070446401c00c0740d41d02e80e0320b44103040c92980082c0c82307010310005401c010407421880d5607070500001c50300540001071500200ba4000741168249441c00d0301c0a11341080b54441d2941c0710103a4500300300f07400250000754502410500b0901b684c070482d00700d81c07030b100d0703036100915040c00401c0003420050f05000b101c62181090325101110fa1325917400311240d000760321000c0e0000c0c0c942030080042d0018030a0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 657898812 1250 657897562 657897571
    0x1e02190311040b270d03080603011104080a0f030c1a0109060f061b150914070608070801060c1e03030209010806040b0a092f040801150b03010b0903010e0d0504081b06040b03 76
    0xf6850440494000344141c8040310061b00821050001c00c0035518080c8900c890079804e030081141410b003000c0901c1d07a0b4641400c0c00409001081c0380b00c005150081e03035421001c9500000404441c154a010400126820303c80c2015141c14030360003290040c241170107213041e10741c10364400242c03c4030101e030700c0e5015161300300613505050940ba240e405445c0500409035601c0c040e04010840340c01c0c0c80c240381d01c0d20b1050740c0020704210254050084040d4800302c441e044075141c1c5072202511406d410301404200a0301810000204041400e07010140c150f0043c00d21020240c8030000d070303591154140025188140c4003203511000e0b0981c2071003400b04652156680002703511843c041c80c3c400d028841050384005086040030700001c2010001c0c000c0034028868500402422461114a401c851018030302040c060058444008184d805403924250b000312100c1c02e2000417a0340b03070070181c60003501d00d130302c203005070642401031030724803c1000b00c0d18480010200c00940f8035031070315292081503412070700080c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 657900062 1250 657898812 657898867
    0x30c03070302070c050406080c0a050a03020616050102090a060c0302100c05091c0203030d02071401091a2e06030e01050910111b070f050102060601020705041e02190311040b 76
    0x1c804a1709480714030400003e042084010201112040e0410844100c0d55010600c42d04041109100680381d203c21380d402c0c542c40445041440c065807900c54068041e00c1c05450308040200d40c0096804c1c1d111841488460294080e030b051201240c00810550708506211300105d4010012580ca40c10b04400c0045c1074003000807400d00c0c0c0d40d25a4000b03819944503100c81011607402043e180144801e0024005105032110000c028402580d65000307a40000c0788000300c5c001038a000007555445180608101d80d4565604106414175940c9400c15160103c0c090400000e25040350014040414810a8000e81406000303104030041943c280b4081d201d00c2001c0d440081092081008000d40449441e809034005c50141822900304007501041c01584d512160440d80100e05024403030760042303002403c3d04c0d4140e80100354850705503020064900001c41d46404144009180d40420320642c00d00c83e000980c9070b50500a07502c41c40d1441c402c4d0300a0340100f50a506041007203c0c21011a4003188107051241c2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 657901312 1250 657900062 657900083
    0xf010513020903060417041e0f080a0302060a05100302093405070f05070e161b1a150303070f02040617060f0a0b04020f0d0b0108090d2a05150c030c0307030207 70
    0x90305071600b10542c4022320007291480d20014003d92a41950f5a005410202d001703040703624003510002d54602d0f0103802a81c4a03a074407004074810102111075840510780141044941d42070500203200003800c4140811550703070500c0080e00b208002203803050b0900b5850340e940c5042c824107849110800c035546004540c03900c42c031000011000d500000341c074441ca0740d1a5a801261075100d0000d4010200380c0c408041211582d0500350014504800301682c1d42c141400400150342e0b0b4a8004000c07121a440182c4c0c14440400d01604001d135207582d62000c280b0a0718207000040c0d032405880d00c3c3c00500b140c00340d00340c2c0019000850066018103251f90056000901048440e02d2030040782c100c0e880402007070b2282400003104c4450b00581c3c082d80100329030a180c21450703850141e013115155000e2000400410103076041c01c0e80d07060000805407414100688688140e01c419240c261742c0c3c1e002c180341100c15080040001010800303400305892099549003811860355454031004c074001c1d480040b0446849003103 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 657902562 1250 657901312 657901319
    0x14010f21061701060902030105060d0c021f02091807171e0a05090f0606101407020604270203090c010f20030405030f010915090f0b0f01051302090306041704 69
    0x314061030006201c107030703501010340400801e4582551125000921040d004100400840e00c40701d04840280100440004110070314080072410820b800c0c4d44510f09600c20210600080340f50f0f80101182101242c0401383d0038600b2035200c0c00706204540000200b8a659141482c074a8034402c1d05030320a00d011807061102e410411003035a0700500b44d4500446959800400a184d8000c11a981c41c0b02c00400092a440c81d0440009002c070500d00d00e00713030420040c5c180c01400c1c1d009050545040f10341c018900313a29a034407800c01042c400749030482d0340741001060b00054603819142c070849009000314005410500f00120043d500160341085881c03c1101d8400454014004040e40d10f500341d410350041c40c1e03070701c2c075040406150108615a2b135240c1d91503e01510000342c0384000340128024600d1000c40d004c40542000f20031101051805011005101c04020341d140014501c18140c1d4000c50751a00b61403c103c103904201d001d243c0c18160141d1080000c240800c1d18016581c0f600d02c030402490307140548 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 657903812 1250 657902562 657902627
    0x20f01230c041d070f0c121107080a050a0204180305040311010c051f0509150121021003020d05011d070c060b03011a0a09020f0d050403020c0d05060406050114010f 72
    0x5000d030404811282200510040300d0707004021020200c5c2500c0e000400c0a80341c1c540140e2042500c010b41c05010b403031428206650f100b4800e01c00200030181c1030b80c0001c119405c01c6a2240140e06041788940c1c900f0380f46003c8440207080602c8115010342c0c803d420b150840e9245566141007842d11814440b10b42800000508104910810f403544680540c165807140c5141c90140d41c0c01904035130031500000c800654036141d0306c14942c1117404030307283d4035500080f619032180e44801070003000e500014080c10040c21150503400800303440c9120b0100b00841d84e61201e03140c0c003060344000c038a02c2d29401c0102041c40e05102e0501c5840850240100040400a41d400030303003158150201012880d41e440c40c0e80c0760500c0d00c895071030005c3c1600181503260420000756661342d03200d8425221840c940c0d8030040340525100304108001d4040260141081541e01d040c06075465074201c1d02110000c1c2003600100b20b103030349451048007000c01030711405034684001d031050b201100303000f980811018010802419007507 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 657905062 1250 657903812 657903839
    0x5010b090a0f060609060e010503180604050714010201090c1e050a08010603020a050402070f2301020307030f051f050d1e03050309120705061b07120f020f01230c04 72
    0x404400c002403542441d00c1240b0540b4040e5102600740b0441c0042006056084241c08140403000d19005942e0750f100c40e000050300011a2100009102e568204020401d0004050341503800f041d040c04020b01c0ca28004a00383c9080a100500101c05040d0400541c1c0e9000e218461265207030591031701c9030752918003145412080da480b600c0c0c0c50703441e10303020015402e0031200380001d0602502c056242012548544440640b0010000c040b41038200500f07913403110400e0060303102d9609200940d0b813400d28480090213402c501c60100d160b1032800c008103400c1903140e2003a4038141103d4942802c81441c010400003901a00321081d160f200303c14184031181402c1203d20703044036120703846d015201c2c01c0c203442161504192007050700b030300b5004101070408a100000c015500c41c3c009124104502c140c404000f4550040c1c0308010400408104207052454000206a110300365590031107001c28811f0310940d081e100784507a9540264464822980714452140003607074001c00984c0e002e440c2035034410760280303400e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 657906312 1250 657905062 657905071
    0x15060b1e1606150902031302060702060c030703050307080115090303030b06090d05160e1306020f0f070507170d051603030b0307090609052508151203071211120705010b09 75
    0xb55a54601400e50f068940ca01501908022500f1400c5183c2440d919910070342245c0064414076003c50700c3e0007103603103c00880e0402c0800c1c0c030503a51242c41919000c1d00c075410a0322403102003118000003044c1110070004410070003c0c26078842104503d10b0b1030030b8005185091181383c0003201003049440c0d40d2514113813114000d00c96001000f8111414140d403c1e031291070b4001101c0400c010301401440090910892021500300c80c00680d1142a030414884900c14074410010949000c18410140000414010201c8902205a40c3c0c2d100e01850003035107400046d01c088000c2a800d2010211158000310305c003545c90b1190400250410010002a10f04441a030100070003a44580d418448180180035254202035044018a00786183c81121a000c1d003e5004c86020010140f001901408940040c220300340409041e00101a50f461030346a100d9001100076600801c183e00803642183c85041c1c0100d4003011400039049950b52500c1c8194a503000d0340c0151655900d41c00300325400c0d07a8816915016 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 657907562 1250 657906312 657906323
    0x40b1b0408031c02070c1a07020901120311010e15040507030c0b0414030c061903061e0617060102301b1603080a0e060c011815060b1e16 60
    0x100d1030070484030401c0f00d800c00840409240180100400178100103421810b50300c1048040c07403290907400441d4211700034410301075884840e0000000b03040e403085134500d015034007a13910b012900500d260000d0a0380d200b20030405060744050134103000243c5011580340c00c540301d1426100c1569503a1a0340444820031703004407110030342c0043c0420400800c03501e02e0806250070f0300170b410f10703101e0940040e14a01609038034403640c182054107800c1c1c0900c60f80c0010050211001046914031500d4000b81e419060380c003d0301d011941c1c218054a2080001c09402d100c2c0d40164000c0960340480003280c07980e06003a011910304540050540b691545040f0301805800191803d010001400e8964503803070980100e08901402c9003a034001c0c0f0205101004607108e0050368184030001c0c1b0703004c50106000b8401e1519103407680d46004408034442c03242003011602caa015400701c00b01070602602000c111780700ea10a1203000b407005c21918140038088100c05440003040700440e42003050084404200c1d4414910885c0c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 657908812 1250 657907562 657907567
    0x1020a05010f0506011d010f1103090a060201020418060305060103060e03070605040b25080a051b030c04090b0916180324050a061a09030c0a030303020d0c0c0803040b1b040803 77
    0x5555902c0740403034801b420000c440003130b03480c550f00010b4180c00307082000a0400c4940005112640010030481c1e0b83c40344040c15600300b040d80c074013009000390002d00a1910f445e103801d1100034850428002c0000356900b12010304510791a55a44800800d0410040d03c0d1170700017401b9003404500f29202e083d118a0140d100d1101c03e14240300302d003802c107a616a00c0d6140314103000480040c030b40d0182540750700c203401710000146516108031115081601907000310300c400000040108040c10700024208560400506002840901d4200109120201ea9a0210000c2020404d07100c500c2188601c1c83c2411540c08561031548a8460a00c5052242c14000604108900f41a44032501c0e12400342c0c000b200c000c04021550070140c0b001b608503c529808c031688a0301154410f41ca503418824417880d018010304d490300e450760f40d180243c0030b500000e880e030055925020184641500482301c90b1a0154010810791460390381b40c1c0c49154014014103031000814907101801721010102c80140701a10032a001540c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 657910062 1250 657908812 657908821
    0x60907141905150c240a090c0f0303030f0e1912050d1b12150b070611030f070216032316090b040b0a0510050a021f09060b15160201020a05010f05 64
    0x501d4075002020051592440a4890b007045e89141141d9800c5010001c0206150195040003000800c0c0c6800001d00510300210000030150560f22043c40c0040d45031042c04560071564402e03403500c1a010300202c0d200c2815480d20005420036025401003510b5080c02410f25000c004000212500c240e0307580c81c86065042502c11080c0c02601030401e1183c0a8420b100003905004600c000500b18070400713004040c081410f2040010315003008586500a0040030b80b240b5102e80510000d800039210080580500021101101120720581c0c1c10390ba00079803000012800d0480244140d01c0c0c5040d011014000c001440300040406503c00004011480001c90002045000c001c01c441064141078814203801104000e141c0325800007503a000d945050040c1c9407015060240d081202401000141e00d003410075101b02003c0a07400000a603000d05010880c1b16200d00a000444101031030034401c402c81800f0f102150803c1000a4010510601c181c9407908095540c05003520f160340b400d0000c0ca6114030401 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 657911312 1250 657910062 657910087
    0x21204020415080705040b120307050d110f070b0f0c0a052d0615010c1b09060e09100c022e050f010b03040b1815010806090714190515 59
    0x2e00d240402c80a800340d900349850b00441c1d50f04160b20403a809941c03a001d684806aa90343e0130b54140342108410b4076a640701900d8180d40741d44400203680c01148010066aa024800050400c5085003480040810701d003020700400d40d5030460802041c80c45802c2001c9004030405000201055219000424807000c010700c0010000c0d20800610000d1105805d0b17404030010009080340d00040440b407018010001000103d030503101d60800901102c880d40403201c8040700302c1c00440200c92146204000c01303a103c50004120900944040f2180c1c0d001600c500c000f88050350041c4840c40490040740e4102c80c030840c51080c0180f1036011800d04507020b03064000c440e00b0500680f035119814610180c02c03981011110341c0303e8000a440600201c41d188000f45100c610301480900c2003034400102c5400425020070b5500000b030901032000d003402150040350210600150002c00d58022200c3d55031303085a210309101d4000080005a044c07032100c2100003075140c440f03002c0340c09061081030a082d030306c03521503041 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 657912562 1250 657911312 657911321
    0x207060f05010911191b050c09130302060402091f0b03150414010915090f051005030c1503092d16030b010311040605040e030d1d07030b18010212040204 67
    0x10118850a00c0d40381042ea9990608485480c1420001004285c3c4400c00460303c0d80000040303546614101e40103c000e0010010f9144a030905c101e500714907a55444801c040400e105800090141e8440c1c8081001807905003043d66010400c50340c1c50f820502e182401c003507082d120b50b020803d04680002444801019400c0b803249040040d42d0502c24127040f1000260796002c144920501190307140800131000b15000781ca1002040700d05401c0c03105003103003120240140020f54000e400b08010311400251414040340c8070048100007006607402d84541e4a8034482035100403c000d6150251070300840550b41c800080c0d807100c0100c2e483c83e40c0300c4601340329003d1500359491081d0782081000c072002c00000389410605419298071040405041100d8408136000d800190402a03105051901200e1090400000f8294030020503a062145039150f1102e0a005601001d07008281e41000e503043c80850443d0604940140c0c850000344d500d681c0d00030245089030403000c001c0c80044180c0040c8415071400e40078 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 657913669 1107 657912562 657912569
    0x3090d030221120a05060102100b0a080d17070e030304120f0c0306020306041802030c010c0c0f0320062a010f06030b040507271d010207060f0501 64
    0x10810701180c102c0b500c01c01c0a0308008001810310f08a90240c5c0b40a60340603005442c1c07098080b0011400f9240d07070030365076030428040000061010300801a03010f0b4540b0319901c1d114000c49074150a0800c16018015400304801207504040c00c3d90040215811102c0f00700140d071141d41c081c41c0c80d00350221409009840800d2444002043c442e0341c3d00118803501c000c81e030800c045103a60384014201d514503a0b000c0c4d01540240b4009000b54000c0410105280c01b4441c5100f01c60743d514000741205501d078204640049059040462031401c1104140e41164120360207400c01600c200403110940d451003030707003150020910040000860a600801e0100034003070050119940b00d0500404408084d2821980f07445140000100c0500080b038550b6600107030355901041a6401c19410054005c21500303a41620f12804280303403040d02407000300980351041e1000305038002180c0300042280d40c140d0 = true := by decide +kernel

theorem cover : BRFrame.Cov 657733812 657913669 := by
  have h0 := BRFrame.cov_init 657733812
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657733812 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 657733812 ≤ n) (h2 : n < 657913669) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
