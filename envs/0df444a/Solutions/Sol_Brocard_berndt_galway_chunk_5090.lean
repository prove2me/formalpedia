-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5090
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:42:59.435287+00:00
-- url     : https://prove2.me/submissions/3c806f52-8d24-42ca-9386-ebd3d571c791

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 915287769 ≤ n < 915467625 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 915289019 1250 915287769 915287773
    0x2034c1112011d090a021309050a0210030f06050f0a09020f1314041802030703080a0309060608070303090b04150804060209130e0709060b09120c09091b0d03080f04020a090e 76
    0x400c07409440f0903c3d4036580305180c2c5024000c00d55a0342d00080500d44241004d640b034503120813040040c0102800408200c541c010300154035002a03440107400340200b41610b807009403a1010010f402c7c1070090b002c07025600b0082c0407480d05810800407000030b4000e503001c01c010250034003400803c0c040300784904016100082d8406031003000c3c3c20810003600c082410001003101081c140300010381740001d2920030389900c01c0045413607005101c4114004c00d400e0f1800340c2540d06281e8001180d881c007040901c241c90180c0d40e405840d07600c4400801092050340b19001c4600c41506034401d484d84120900c3c0d03040ba2040b800036141051301e03c001525021384041913820035031703210342001c0d00880c2048004020904820305018103481c0241c1e02001d0f000b648488d50003180080c400032003008081c4038007489082e0003005084141040c004140c0d8400c1502c45401c00c0308a480c031102498544071a20500041d070540ea8071010b42d0f5040180320902d00e0140c412a001024540f002c10031341d03281e00400421a0310500 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 915290269 1250 915289019 915289049
    0xa0e100312030509010c050906191e08040b060306010305060a1512080a17011809050709050709090c0e0d0303090201121a03070f030b041e02034c111201 67
    0x25421140b00f1b0502c03005028081141080a40fa03000645280544188403817407550f24150342910a684100e043c2c20001c13050001512a45812541c1e03a030040307010720300450141da110740906954440a0002130a80d174084000500c44240340d4000000c3c0056035070328804926035541806c0390030044079808550400e804100d0004003580141e02c80502c012075a03e42419514018400d0103034076040764404817282c0c64040c640d040c040108100c81c01000008001c1040e80b03040c600041981d185401002600c60138100c084522a1142c2d8504210318002060303482d4070702c0c2a6074243d00601c1500d900700e05000c4480c0c40405140298031440310801403101505c0e4000703403504101410081107803c039090050b01d000e001c0c000b090401060f50740c815440300d4140f0825005449100310640d22a000039410310550784104418440480302c0c0c0b0703c51038070032956060044492024441d02c0e8450b07d6070312a000c0510003010807030403260003442aa6207811103a618102892802014243c4241c004804041050f4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 915291519 1250 915290269 915290281
    0x103031707030908030a0b040b12010915020702030d0503091e06011e031707050304360e06040204050a0f0603050114070207030803240306040f020f0a050a0e1003120305 74
    0x16401580c801d00700d01d010080a01c26136900d03e0140405002503400b1503440050000fa07880f1a44140700b03911000300b0515200d042140414007a1032030120032641000005041e81e5540501d000303540c88594020054902c0c1e08042000b110380341c00041c0007403404d100d10b0411b07400003449020100c055020140252a140d030604080d01901c09505505a10500d040030040000c95596080c0002107204240c2240d50340302c20741840c501d18002e0f9081089801014002c0103c00351600b07120502d00303e5070841049000d210080780c2c500b11402100f83e40c00036040503001a0040c603003a48120f43c0010000d1002641040d5100c04208449564004543c10b0f9518110700e00344076040760280c0c2d84080e042c802000d84500f550380c1c030111404090001c0b20610700d4642124491600105c06480d4028003900b00d0f00c41d0b14041c2041c3c510b00e410900141d000d10800c07524680325041c030301c000d0825144003030546200c0500d855002c160304038005101c6000d0880350200480000e900d03100c0e8000d94078840d503000c100c41c1844 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 915292769 1250 915291519 915291557
    0x150e040207060b09010b0a02120703031b080406061703180a1a04090f110a1409061606111e1602090405030304030315030c03120e042d05040c2705010303 67
    0x46e000301c01d03914001d0003c2080075500007203030700800c5a451241078841d601413030168080c00b807200712081003047c7d8564004a5660110020b13105500a000600c209039840d10328244800381070b5003130242c6400400246604c10b150845025103814040d140e0404141c1d101180800c0c020745540f04422801b0002e0104031076042c500070500200d000580400040c11035884203172040c86140d0b010010701690b1079410f044203003544103903403180c4406060680c0e500d622005440d00456031090172960346142151100d0402c206100f520107010781d21200400b403241e101d034002015001902d9890320080b443c000440180c0f200a00c03140503510440040d80c903410070740760160640d10050500031441c42c5601c010004600c032401400304513604a0010030199441d03500c102c44601911030225081418400f07400e1f2030064021240560541c0d810036950071a07800c004500544106881c050480704a00e5414401240c2501d100034041c0680c44002500b80b802c10904416154264000d0340400ea00b002c0b00903040c00e00e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 915294019 1250 915292769 915292771
    0x9080d02210903210705030a0302031611060622020f0306011209030f0c060e060411010f0c0b011401050417070f0b09011706030a022211030907150e040207060b09 71
    0xa0441e900782007009910100c1c0e50740e1241a100d424411005900c030403010030308011615015080815282d035051a5040a00a90b00c1664006000c2803003c400d42d41072032203510203005903400391014103059164001004081600010105001d9028003100484000c151000700318078411f08070000c4d2280b03002d01c0050b01e840c1e0088100c000e03071800c2445030000a0391005011980008900744800800310a0401d14010314996402d0881e61040313509020601c150b896500d407989400741e0360b404109584043c11110000d001034005c0032040918014000e2244040a0701980241854083d0501d6691824002005126130007024507401928040c400700c021101c440307001d030130103111180c54220203a00080030307154440700d040541080400800c129540a1000d00c8145070018107143d000903461004884c500d0107003800301d00d01c070b2910314880ca4075030580055034071504250303010301602490620454015000e100f11a003c000110b00394000750740d03c80c406442014001d50000505a941005201c030203a0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 915295269 1250 915294019 915294073
    0x100b0f0a030308070525150c09050915040b100309110103090203060a150b040303110609190f0c0306060b0915190e060d02030405150c120f0709080d02 66
    0x2080050500200c0d400c07000c201e81040040c64613036550100c040414045428021b00d00094a09074000002030000500130b2039001843c008040008054840d81138070b51048a200e0250080c0f200c400251981c4e45840d021558154090030204080c04c52000140c81c0184690007000425034902c078100038400e030040c28911003170003070904111401d0207400080d980d14000303100850f242d842c2c1003440041034502008200030202d207200c890300c441e01c0380381c054544440d00035200c3d00c51140c0c00008605050010302d090f503c54681c00e601b03804420a880301d45155054100c00c1d502d40049190000c00250346100d108004c201d0714101d81d845810850821688880340000d400005809024440c0c0d01220341a226840b44550704009010003e500c000c14100c0c0101d0001c0341d0340e588088201f10034084003241e0b0359200d0b4820a0b52800554070100751606a00810a64245402d0031100040c001c00344070303480c19007003480e600b044841d4030340e1115082d00d0480c4401200c001a08812400042060700014618010b1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 915296519 1250 915295269 915295279
    0x1060501031a0607321b090f090325140c0609040e070806070804020102070b0301060c060f18030e01021e0c060f0705030a020a1a190c02010b03100b0f 66
    0x6180360b51075084000c28500b014452040040c1c0c0c4020881c000042c4240200000b40701d035150301c41e803d00c4400d112940b40307040801d0300980034001500c040810750aa078104000340003107001d481c3c60854812002c402801041e0500c002c0041542060b0a26108665038240303113104c44d00c0b85018070f004000440366242c40080740d486000340e00d0440d03503000c06960010030203070f07800901214038826451402280c4d6002c022240641c07000c1c0041c00f41d1008041780b003a4001e8003215078013566000c41680c3c51200b44500b900085600b1007150000384c040d00109050505008081028076000e8a007500001c0c00e41e00480c0851034121a08415503014000030350b0b0090000341d1540d000003d10710ac01d4940701d80c2c03101240310b10000180d10040c9031044059070559070b0003d00301c90f100c0c8441ca0010755070b11511181510013544800764298101c01c0540318905c14000d420681990102c50040e081c050300714002a0000e5540f2030303070004910b840800c003c80c0d201301c000c100400c2101c0c0743c0040c4682640124110740c025 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 915297769 1250 915296519 915296531
    0x609022d0a080d08070e0d02150d0b01050a1706120d2001060f050409080f070b01080c0d0f0b0907120804150201090b070c1b060c060e0706091a0c0105090f0106050103 73
    0x70b0f0740001c410342d4000020305103146c404021100203412100c060b14003c1d40244104251646094030402030b1602d030b12040703010490340071035000542d554050b6032205800160354480340001004c0440b2110741044000d0841400581d4052010342866000320203080003542c2419001207002d48009004507815100000300072880c10045402607400c0e040c050030307000301c3d1160444010001101304440ca903445000005899891528015039480c2080c401c072421403140710000000c51a100040f1841c440e40800702e00429000703a55030002540c40100316020034003c4141c0068500200c046c80155144030360311081d0b460b0304001e000b5004c2c1c80030050740801c5a01d001003103c002900345181c940c20828034280031440d0002072400000040944010400c19450300c240000c80e19000100c082c0681d20800f030a100b10030320718901e01d680301d01c2e5202c0d00c800107144410403c900c80d80c658910781d095034003040807854007181105027406d591041d5001d0050754420b004007882c3c40c200b0300ca00406004246402c0c440 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 915299019 1250 915297769 915297793
    0x312091e0b06091303030203040c15050a030c08010b090d020a051509190305070303111c050c010c1d21190201020d0809030904020f07021909061703070609022d0a08 72
    0x44010604030040c01d241c7d000010805101c045524134004000c020011440300c81c1c5400024800d41000300e012020908024561203a00d0255804a040c2d40d84401c07094100400802000070103410144140e070404030b09080461030b61a0000110300081840303521a5507640c000b014081803610034204894a8800c4400070310000d04041250000c8030380516000c814110b6610760b46080c12064544c40403c00040d5001000040d080030207440f07544041c3d0020014410206015a501882401100381d0f07598500c0362042c0c589010425502500102c1414200e1403070f8041441c2d2030310346031044800070140108408011503a0402079400092001d14005d00b6900742110201c0e504d008503c0550310aa40115210051100c04000d0301c01c03107600184180135030b940c2501060818071950052540850a100c03010034800d032008440001c07100d00d400290b01d03020440e11540024900000100d078400741000002c599000321281450003942e07240440c1c100840014100211003503607a102d010550015000800 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 915300269 1250 915299019 915299041
    0x10020405030c040b150c0a06111c0f06030209040609020a05011b230a121e0806091b0318010522030f02010e010e071509120312091e0b0609 61
    0x3010318420744000c01d04d0f07021a000160800b40c0a120440150000b10318010000c05c0014040e40442c002c0c0c030100a0507440c01c0020340b261048580d100d401411311b0041e4582c001140d801600d940e0380d500000515070f900e0b580011100f03030040d00c003a51102d84410303880096240881101005113002d09040d203504c8140c0d0345072880c01d140088050f14840c400c2880c01030000460300080c2c0810074104c02c1d90240c0035186400b5405e009040e21304000a8400091006040e060245454259825440700461680d5070030402c12107540c02480b40c008409245050b80b6039203507010185000d0003030098200303010718040c540c036401c490000742040c0d8110152031844500c00e100c0c1c80010340082d0503180c0181c042404a005074090890884c0034140d96180035440d41c4444404500c0705c054a400b8602e8054a180860003200c2c6805107020b500100c864180a0200107801042a9144901944030100d40318125450f405188a0100304008002038440810390802c905e441c0d4107030f4000c00444040e0350302e017060341c0129 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 915301519 1250 915300269 915300283
    0x6010306050901090b0d0b07050310150203070b0907090c080910050f0112110613060908120301061d1504060e0a0303140a030e011a090a020c0a060906020c010f0203091002040503 78
    0x1105599451046840f40c40700200001c4541d08818003d01f00e09200780c0040090f0b004840310305c44900c01703220101c0c0c01468920054141b8030158021800d00319a52144548044050007180040c80707003e0001034a00403038040c000d4481c00545034500ca0b031034001e20b980e09203219807454040b01032800041100383c1c00d500e940607055500750f00071810105050b1070840390500d80000b0b80796014402240c00d1040c607001008407005c1d1041650b07080301040c0c0d10300d4103594480141002103c0d550040c0010310407640318200302c44140b40c3da40410801603030900b0100c5d8114000d090b41c48600c080c0054140125500001907041c0d00e0400d454040da55071450300c000300b0100c6981382c41d8207038407400a024071402d40309400400c6101c216400800c01101c1139010100c0314503442504500813200789000030040c0070f580c429580061300600240c13040855540e10701c0020180d10004a424a03800d010312880c544d42482a012101442480103a8030308211602d0391a101d00032a10404e0f0a004000a21003510081400 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 915302769 1250 915301519 915301529
    0x6020606030a0b0403030f0f0b24040510021905010f0c021c05090a08070909050607020307031b0206070b0a2c030d020f0c030c0102071b0501051204150f0209040506010306050901 78
    0x1c3c90710b54549140c00c0340680000b401409003942400240000c101141d40080320b80e00c070480f6200441c0d02c1c2160041e007183c44001048064180521080246040070100042c01503110f1054940c009c81d021280707842d1000e8100150b032607039501c0741c540d089020719100b248100d854600007450540c09410041e000d0f9205c00c980b000800c140460b00304c11988554168802900e4800140c3c0c611540b11207810313005200300d030020355144c0719410107d4101030003c402c86003411b070940d4850710b40b4160681d4240e034100d01720008a0700410301700701000101d401e128195010392080c040106c0c40920303040c241d00c10003000c82011840742800304241548a1000130485409210034000580c6078590f280301141c1d50f00a08076000e0080c00b0004080119400650080800903ca0520407c8260b8172013540c541d508242d000d500d0100b80d08129840c0907030342d103040c000d600500c501c50aa070ba120040400034207681c6082e43c0074440540104920300300f480c19004450b400a000e02e0304001240c03034240042c00108040c440c03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 915304019 1250 915302769 915302783
    0x60614040e07031a0406091e15031415090d0206090601080c010e06040e0403020709110301120308061207062d020c130b180115033308070b0307080106020606030a 71
    0x40584e8000300e12600035110040140704001880e0f445030f121018107004d174018074400c880f0f40051180f8070354078410b112074144010004061a811540c50703900c50540180d400d00c446c03040510507404802d180105510801046c80038000031200e01c900649811070142c62100240c00c0075006000c4c140000455402c200300900c0c213980300d03221003001701d50302d40300342d401c1070b4000800c1e00e00b040709140e00001d07001c2c11100b955201300034840c8900c0c25070080340820701455034582104100b102c0441e1080e0413198003e000108a2081d219902c151580b900760700d0341c0140081601000c01c0280609001c92220f01e158540346181041c0c0360800340251941d502d4403007503200e0029005609a01d80c016880180c009501415000b000c540001e2441c05580091040318881c0c219004011a00d51081c016a00c1064414440e9444507504040250300071404020b03400356182101000101c6902c200303d1440180f1803005400d0340c0342400c0c14000c3c403030413058100c0f50941d0702230428070802c1d480000f1110700c501c2d00604 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 915305269 1250 915304019 915304031
    0x3010b07150c23090a0603050105090c0a09180b041505180f07051309051302270c0f09090c03040c061707140c03071211010c120c0e1201060614040e0703 67
    0x2075a00ca0b8003a44540c182c00c102c1c0c1700c2010400359007681c801416034800b25501200d5640d00e00c001e80e194419440024009078941c681000100100c5889101b01c1c0341d48500481d01c0d4048030003180484407111500700840095031010021806c141d03500560002d040a0b003580c0d1840c040050761500203010348400204000000c0c0110f50b2011a00c0c150054001090b06005a007015a900d0084401e00c4100fa840341d80039601080701c21102090314080300369800c0307940c00a07036291803201c1c1c100e401181c000071410034200005605d079500c07504650b11820032101c1e01510783c1880d0a282c4801099502709006020f02c0005102e500c1c041100c07050b52010031440d04d04000114800d441440340620601881c051002003801d0f810000700c4058144043c203242d88200008010b100180d0036508584100008241c00c2d18844501400a0300510800d00e49418100c00400c0640040352004101030401c50050750755690911065500ca250169501d1401411074101418000004441d9101400120605903038030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 915306519 1250 915305269 915305327
    0x6040b090d110d1a0105060a0f0e040b030706020601090b0d081207020307020d05151b070f05070e180f03040605030a2003091f020c0a0210050d0203010b07150c 70
    0x610610b80096010748819060091031400b194800a2244e42075032162041002080034100902950481191603030b030a40907091580069030170080807409150040d440b02d406000f0b84e10100240360003000c0f6076000f81540d607d8a107415088030a4018200c0c07242148031381440c04518020305641d42c009024401109989035100103038a10701c26604029003003030be544503200512002017a800e180300c204915408895440646003136042c01d4010302e081c2c403000700380303c1140890040009042c2440c450800c540e0030603102c038a050301d140d40441d90304800064584401c08004818080201c040e580040203500f0a070800101810501008040000d52982c2d441070304843c2c100740d400503040c090303417520840e03503414442c2403a0340b91101c3c500383e4190034007040c508031040b00d09e601c04c96078240170500141050242c240c3c00c004042007920041010401c0c00d0007070300603403612840254000d0842030006607941c841ca14140c1081c424880c0301c4e01d07150380f81c40110018540c00039050181400707080075003c01c182e012 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 915307769 1250 915306519 915306533
    0xe040b0f010f030b1e2806050c160906061106010303093011010912020a0b071a010617010603021204080d0e100506030c0d2001030b040218040b06040b090d 68
    0x40b00b44c0307139019004220102c2c124200f240b50402e080e10a44406200d0548803400c049054003022440c2e1480b00c07584020880c0781e10450240100c2c405410541709090040c611020f81c1650541060044a5840c002001955000081d60801c00580c5001c0c00540d0b241d524040c3c002c4c0712902c0b65a89500c4000d9282403015010304a1107003413403101d403a03014108100e0408408006180750540c0c04248550004607084c94112040d50455500801041c1081d0520080d0511600100400c641e41600c0030310850801928580244c080d0482c1c1c1d81d42c01044542d00685403d41e03c042e8028401e041c0b04010641c040c0c1d115a44c4641d0064000c904503958121108441008000d086407103101401240c03003909040c1c4081d04414051842181190200b1a480702081031000c80c10000038480084160024000318218040b10201c100504002a01c507024002260a03030f8441510200c8460080300003550341d2505105050000c2401c2e2813150070a801c104207031032244901c0c00114407032179400012000700511 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 915309019 1250 915307769 915307781
    0x101d070f1d0a060e07080f06240a05070b010b0304050709060803031f08010c050c0105010b1204030e0f0a09020705060702010204050d0f0206133b060d111f0e040b0f010f03 75
    0x80a1410091485c203d4802000078400384c402c00201042c407404103071586008a1510210b00d0344034480c90000190400d00c04030350344038000310001d03c00288418004186c00b6080180201075081d082542c91515181403410440c03550002d1990074070f400c0040c0702889001041d01d40c03202110b0300b11441000c0361555035240c040d159112403280d6007020b0b078408080354004098100414210001e2000e81d80324000300c0018022000801c1d21141d0690020f03000c640700c0c0018403001e000207030094000c0282c04000c04c1c107070a581d81143c1c0c007040c0c0000c0c0200c10041d0412010f944154644000c40c00c0904000002e45142e08510700076101e07210b241510025507403504110751420090094031a003607541d400ea89443d03500c6002405145200113190024075078803c0b040c5408801d11400740d20340a940305401c02041c07060610040c0c0710b240c4410b0240089031a61030170902802d08444101c00c0c403c495484c020306614001c1c903214019810040615440c1e1102a00c07200810307001d08221070704140d410000c400401c8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 915310269 1250 915309019 915309029
    0xc030818060a091112030a0c06060509010306051e100b0a181511030f090904050f0f160506130b0903030c0106030b010e0703022a101d070f1d0a06 64
    0x749000384014551960300044405204020740b20142d1a404200300c004043c400250301660010065800032901c19040030780004e2003580c000072050346400c045010323150243c00881e080c6680c0d00c18440500b160b0011450046000403c0440034642111340c4005003400d44681078656201181c160310031801480328142404c00306030210511590f420b0b030342c81220b031440082030120702c030a460292080404003c45542c0b4a51001741890090f544091145843e801402924103000324205070036450320a2129025900c1080010404120b01e400790b41c1c054030480c1e100c40c1c4124420041c031850200c1c2c00395988212008550b10544409040700441e05502c144107104410f0b51a11502004011040382c000703040e60320003501074280341d41e032000540c1203100701034850710780c0e03203011007252580814001c02d0940c1800000c1a40c61b41c00c00d12043c03800390ba051601d50500c481c86255003400d40c800801030807000301600c90351542c0861030250304a001403e0405207000b000c42200005c5c001c0c65850f004500102 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 915311519 1250 915310269 915310273
    0x22b02090301150306052203450b0a02120d0902060a02030d1503050a1401021b010e06090a120813080a0e12030f040b030619060207080606010c030c030818 68
    0x10340e810f400042441c2c090700089943c6440c00004c80d10030400c2c80018028050098000b5407407000f41d8405481d0100c1d983e26502503c21001c1c8500d201400702c90410081c0040b81780c4440c485035180b9410420513000303820601000c0703018072061250a600050f43d030010140d80721401c0d51488851090009006607800c040d4008200084010190360300000400b0514410103040100c5800c1d000c0c00c4c1d250a45520024145522228080740451480d2100300d00c810603010006280c480350085504120603c002072140c1659180c03200a04032000f880300701e500000100281c06500c0c410b95849151501415451080200030400904806058003510314200c0c4c0107014141c48101c907440080071a510b07007a5240c015081941d04110051000007550713228840301700d0b03246c101424014102581e40005003416031249021509411a801c492040000b40c50181e010f0b182450514040074580072014000504020080c1031020110b903018100c2c903401c0380e051030302d801c0507220801903107051003603031145030704c94 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 915312769 1250 915311519 915311531
    0x190e1503070804060605041a01030e070f0902040806060f0a0308030c040b030406020403061b1202090310020f030624040e060f03072601060b0301090b0d080f1c022b02090301 76
    0x5400126880c4114490341307040c060640c4a41c02e00054908454880c50b00c548201080d40f1598003a801104507040000200c404040ea1240002c0140007582e00408405500140500030803c043c010154803e0081d03da100600d003100b03020620400d00d03440041c00d0114007001158880520b0400c0b24018248100d0107a02c82c141410701c400258824801100c01500e4142c64242111400e0341a50070403250b51601140688001440006075000041207545030041c0480c10740002042e10240c4000c009912080d078070b0346496000d010680448241880034000491007003080b8402c01c00490701a80c0d0264140310254a0346d10100c2c494102c0e1559245c1e140c0198003011550752265a881918804c17402e030440c3c000107440f40c0c001d08aa01d24051030150080400040c040c110341c5402906407020b014180054040d00c90b1520400c5412411010100c20400600d00403804014848181040c5620800718500290246500324541c03001491b006581031124240503110b40303d0b41a2402031501030024440c2c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 915314019 1250 915312769 915312781
    0xc01061518051318080d06170f0a060b010201111308070501141903060e0f040c050f0f210a0506060a14130b040b040c0504170a03230d1a01030c0302190e1503 69
    0x6880280550341c44070388108d00322002d44000280c10801b040d6180e004e85064030b280c0d01c6400140c5280c2c054a8103540d264069000400580d200800c28802c1c1203000314a0107040900e842d0a29103e035104d6070420a960074138540d070034030f03100c100d44103514a403c01c0511013141c0041035015140d15401000585111401c00c000030743d1600c0407c3c4528812070300c42100b5500c8104022200342514000784e041582a041484142400785151013000741e01a002d05404c118001c00038500200d40341d048801e80c100809001c41c6041100c000005840302440603e80311204d1400b00b0b104015051a03200707a107031901180082a1129405002c030800050300078800c2d41001b00703010304240d005204503155502d417003480740710242d400b0400910b0542d0543c0c0c0c41f20242042e680151604c2500945000030000400003001a0012840340d510400003080c0c22030b0306a02180000350031141c00c3c044010502d801004210404e0041c00c03001c0c0300b140c0507400d03c4e0140900c46000714242d0603240380421007a01c400070500503 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 915315269 1250 915314019 915314021
    0x151205150a051e120a08030c04080c01021903030f0f020414011d0f0d170427050403020601051905040c0302032a0f0d020c01061518051318080d 63
    0x2403101000d0796008180c1d9903840900042604074689141e19072500548a000f80c640401109016010310045030320855184e12841040d40c0240c5080c0c2c0030800025040090350300034800011240303000d0010b80261280081020951299070b00010200b6a643d581000064210750003646034482940d811034a0300e0310741f0300700c0a281c3c0580500c00e0100b42006420000c0ea65820f00040c3c685a02421101d03610301440c06115213145420070450398003403500071340506560720001600080030310032400c00960468414403074036130340c1407224401c0b03950500e020480403a40004c0e810741181c009460269100f0400c500c042c085a4541c0c212070741c448e00701842d6800c059450340156024200c1d80702c900f02d600c3c1e1100f60480381c1149100700049240c2080c44403817403c8100a000d48100703080c88201600e090b64042c011400c443c16900b100c07800329120000c001d96154401e13100e040c5103141c01d440b80441403d10001402c0345030092520003d070b41d2620b8440100358070400d20010b1540c0c0c0024001c0c1c80e0007800741c2441c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 915316519 1250 915315269 915315301
    0x270e0c01111912110109050d05070c030b0907090501090e0a02010f050409050f0f010f0f09050a0219080a050a1808072a061404031e06180f0507060207030c151205 71
    0x40c00503111000c0d04001300700c11304c42c4640296000000b4200d041020b00c0c103031082e0304008001e6400950b030410010108204842c842e110301d002c1000380800300c5c2400b1030b06007103403010303040180105c1c40d001114000ca5400103003444442d8090070802e141120019045802e4031440c0c01030081c00b0304180c01d02031808900005140103581600900c07400788c0c0c0703840341307c0da05c0140f911070002000040b001c00c009031400c43d031000e6044001c2c41e601510f00065000c1c0342050320103d8910034000303104c6000b0001801d00d0780c4550713600005e0f05030703003805111514420003201c03000518018054420002d01c0c241009082d0707520540380450030804400040c0310000049003d070452240c000468038070405480e400603824111420307a80d00600090200a28a540c40c2c1041d0f00c000b000c41e03440e590f540011240030380c41400001440d10640b0103510860403450094113007681540040c00790350000f00c4c280001590f48440300c05545400040507a036031200c41b02128840721504040d41c0d00c0b4900018407061107600e8183d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 915317769 1250 915316519 915316553
    0x30d02070515060603010b031015170601080610031e23060307210303060810060512150112050c090c091212190c0507270e0c011119 58
    0x40d8050110402410145810483c0c1296002e0410001400711414138806075401904805005480036202c3c1403440d0700c1d142c900383c40408a10401c0b01d00f00c00c0309a03d260359a1180d007c2c84c020003113050910101e000c6110340e104000a0584806202805030b105140f141c840c540c82a00920120300c08464a011650151510389560341510000540504001507043c1c115540140f0f40340c0041c0d265484e400201c54645411410180c5600e00001d20036001c1107900000030b071721038002070003031310349810020765200c02c00d0301c1e2405801803080d8801070000c06450034110794040299100070055071030001d0030501150101e03940084030009024141a40c0006440c501205541034800d0303071403601c103140c1d4a82244c0b84c4108025000c00001103840c0c031483c0340c03e03d11040350411a00405866a03160b0400c940754115007070a1007584040d40c52800400740d54089141600810440c08001c9401146c0b01d01400d0003680c1440003050700350341c80d40302c02c204903d54041142d0702d0f00014101d0f8501940302c00070040c60 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 915319019 1250 915317769 915317773
    0xf0215180709090b130807140c04180b06011812031709030315011202130e1605161b0302040f090b061c060c05222126040503030d020705 60
    0x440d803002c0d5481403003003454001d091180300303584c0d48191506032461448100c40043c01400798200045c1d000c45140200c00b15440a0540c1103815414042103440c0089013615260400100368041450382551542050080c45e000c6d0701d8100d00d104070f80e01203500c4d50111050b1a04d5060440503d58000503864030280004c100041c56210501c2040e039a001c01d81c0d130800c0d10b044050f00c041030b541c0a40c43e0b003103121191000140c2054070000031117244501c0f640c00703814440c02e0312041142c029540c0c2040c05140c0c180703091003401d0212981c40d07880400d4408100070300c42c10308102003200c03003001c00c4140e100446c3d006005020003403120700001c02400c441401215600345110204060f80f03440c0ea844e150340c21444082000030043c03a03c906028003074214a200078014104901d200c1e90202c0801d0160b4400c0c4100b040400794585070b01d80c1c0c040c0340c0d1841045018403400385d80400042c15601e00007941740040b500c00008050300c020030200c0e8440c41d44403a030701d440300048581200c0c10715005802103d0207901 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 915320269 1250 915319019 915319033
    0xd140919060f02070e010e070c03181205060705190e1804030c11041a0103020d0204120b0403081e13060605040204121104020304030e0907180e010e070e100f021518 72
    0x1007400f1090300f1f016681d201d041e0500082c10b803a105034808100e890091820003d5a107070f6987c501c403d00496009501170000b1540b6038018810f00304040381c4c1004a62400c1c503c0c0401003001d00045030b401030008402c000140040940070754500044030100b00340300741304150700e051030b14000d080d4092007502100d00c92010302c3d610f952803810740f15640c05000c010004100c400600401103009500480f1b803020007540c20b00c80800c0549408281c0ca010b03034850034005409060605015000310340041140174140980c1036241d1000f540c1007900c0740c0000e051090300e0540b240c90715085010344026003040d6003107440070500003820070607412400814ad01404461540001001c28442a44011100139002c15040c200146183c213141401c990b01c2803151524a0b4040c96028090076a0016541709144103428040188090444e81007420741000705410054021040300c0041500a1000203d400c00d01075881c84040c0300900034000c802c082c0306030303022400062812000114091a0302c403080007072881905 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 915321519 1250 915320269 915320279
    0x1305010f0b090601090e16090f03081c02041a16120801150c110603060607062406020c03100e0304050916022401121406070f0206090d140919060f0207 66
    0x20302c0c0c00d081d207406c50341080301075851074018882003c099200000f08600f6000000d14040203c844801030341c880d0021035903d180540603541600344200740810458130400c002c020840e00c00c04042540d0302c02d0085540c5030003003c104c410000000c441d024241c000d4004070b010b0350b181d1060006044c1c80c1c5524041107550441d07941201c6282c40b035000142108102042c1018620741031001e140d220400400c4c151a10140759114026100590458490788602d02c41046003502c20b4005003002e0705480c8000c00502c500e481c002595901020035000384203641e03a044003407228091088401800000e891286503007041c0701c01220f04060140814014044c801a0120358909420315142040e50281d135402281d0800428407140f20500e08100d8020450356140ca030060303001d10039144a045c543e06d504e03032481c013a87c2c8003070f0401400074140192504074022030b108441d08020031802007000b000d082c41d00e4055020210384011103914402a015030107150015030154810140303401503c0d2035003981c0c0410b80c0ea07 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 915322769 1250 915321519 915321527
    0x20310050a090e0303130f020d06020913020c060f0c09040c0818060c22090c080603010e0706140c1e030315030307150e070306111810020d081305010f0b090601 70
    0x200c3c40f020300ca41c0040000c10310641c0030840310304400d806810b0f07050081c415640014000003285904a51154000c00d0415062505440301500546a040150b11303000c4514003458640400030800800e0b00344620215540d034120006a0b5001e60b4054002c12119031505070103480120211100400c502482d881d02850f85004128180142d9960b40c1007418411307042810350000c402080c0400b0341c44e002c4500000c60551078081d030303d03e0b4130045c0c5444c1e802d800c0103014103094881d00c221070080c0f03a00c1680100002680414201c03400303483e00381c68644035903074480b40c030341050000da254940d043c003589403010901ca8048025405803150a0322080d20009a4051507100d001d100c801a2600208030032212081078250014045142a501503424081c0c595403000101e8040000d0f0b80c8900c44003060000944950081c111004c0d03004460091040218207002950760000e441c5000c104109140803034600750100356042c149a501c10020310954514081c403074000c200790f0680c0c2c0e04c5580b03014049000f039406 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 915324019 1250 915322769 915322781
    0x21030c03090f0301060e180307061b1e0801050d081c021207020c06040504111306020106081002090a03230114040c0e06101d1201050402030105010e0f0a090f06020310050a09 76
    0x541c040386980d5070302499201f01002039003c00c1140800c00520b00042d1581c4508820341003400300741051205043c100421982e071100540c804841414070071102c1c2038001c0d0415046a81c12561281d000007a442c01041c0383c082d0700c200c03d0002e00b40c10310600c14071925802410000e070860075800020b90300d10a00f01d96800b00509000e811210401c42846281065000410305400c0c01e00e4203481c2c443c00742802003d00d512940404010b03503441000b40308010040c0240c0d180541c030f0200a50a01042c0d500040c0708c181c039480028400070050f00b85142c1008880b160b80810f01c0c00754020031010044280b041d9041504a800325a661900f40022800000c010043d074002c031000792070510400c3d03100e00c0a0314001900d034601d4040406400f080011644c43c2080c042e59411900c0c0045003e040c05e105040c2500c03c10307040701e2840500002040908000c003104541e02042010010400c00540c0c284070400411050010307006600000402c01400b120031a02c404803601902c00300c2d0119031303030904501204c00c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 915325269 1250 915324019 915324029
    0x7060b0607080702042a0207090608031314040902061309050708191a19090e03070201052d040e0702070b090f210a0c09060b12010521030c03090f030106 67
    0x102c144102400344c1013513400803040760800c41c4072915006100480c041c4c0200000342c9a80140d00c60b1401303000d641802c0c00b0b91002404e2460042d41082c041c3c1079040c061b010380740242d448590815607844407079512900f0428134250090728481d0b0302c0741d020210000507001400b40030929802e080c08124003c1c840d140c41480340100344980c803140d4240154440c0985822000c3c501c0c1054822921009603498001128201a84600448205140a51a0050701c0c07003003800c0182c5420030300c0b61318090703608075044a40221030540c0c12040c042902d0b40c1a49003131b1000840c0301e024280400c010507541d880340c092601400c859000c07112040d540301c150780414480c41c810180c00c100c411090302010309184442d0075801d4060b01200c5130707802140b4440d901d010b03c00315054402c06035075841000301103001d00c100b101920012605500e40802e1259401560406203c0c03540501c2d001501d955400c01d02115188598000c01d0039256101d440280081e5a6000800c2052147c00c0c120712201207403405226440880d5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 915326519 1250 915325269 915325283
    0xe0a060605070b04080c070e07170a0c020d230a030e0f0105101206060302040c18060c0b190b030d0e0a06050301080c01030207020d050105160e092802040308040b07060b0607 76
    0x44e4681d551100700d43c03c20051050b0b18851170901065101d61961040e20640c0a55a0030383c0a090701022000d0200c000303888881c800d881c01160290581c1e0200760b10501e04617a00741044181139882c112103907840118822243c042001c074100e42143d606810403003258603074004030b4004403540142542240d0007900d5200a0440e00c4408000d41080d040540024600035400001c1469503a0041790582d14440050800540840340c0c0308540104491180050001440c01d054070365116074440c080024042c00d80304441c50381d089074800c21442030304490301a444c09826580198500d403006083c06525801c01d0388200600341011900c0c0d07102e10140c80c12120070b02c0003040140208001940294070507013051341c01c05011030321040400c01c02d0082900926085408503500f0080f1500208124444a040d602c220211401d004150001d070071014140c2000080c81ca0502260351180c1d4000d2043c0e5100910540380442c001441d455210050114180070704030034040ca065410400269201c0d80308020614 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 915327769 1250 915326519 915326521
    0x9050d110f3a080106032d0e07080d050f18120a060b010c15090f0b0c0306040f020309030306042a080f1305062a030f0712050105010c03180b040e0a060605070b 70
    0x80b03201f6000509600d04924000c410b0780ca65100400507d001c0034030080c8103e03103611882c00701410403ca101e00400801c40a071500c1140c0d040d0051041c8514844003c1520000c42c0d0006014004200915200c01c000d01d1100703020300c42c51146484a24000050710b1081c074200d41e00c0421b500404000340050750141c1503030103144001000100130010044242e4140c40016134060000303143c1241d242c011030701408140d443e0700d0705130200815510000800401c80f4010700c140144d81100100350790b0880004c65000c1510141240c510a06030000120f0b000321419600c42c1859494025100c80c4c01885001001c4c1c410b651600d000708944403882d2002801d5034400000100100c000400c0700a040c02c1800c00c826a2841b0103000c00340e141c0040d5010b07070340e9001120600100315005064018401c511070024012989010006011280c1042020f0148040c0c04a00c6108007001c4017100081e00c40010301944030340e1540080c051a000840e2031094007440e00901281e031302c0c0110705881407103034014902c0c0c2203 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 915329019 1250 915327769 915327779
    0x6090e0c040e012004030c0f03151a0303160c0b16120e31050603060c0a110708060405190512090d06050a0203060f0409050d110f3a0801 60
    0x4041c401a110742c0741d503850000c0814042200211565480034100860303c1d1421402c03c074820b031169600c03030303441105000c10401c00105190550600000c0070b880002e0350442c0041302100000c01c070400554903002c000b07003000042e0341040301801c0150190408240b80d980700c0c4c1d5243c00c3c40c80b030281103150030000c40d11400d0008490426007a26a800c5150ad02401c10100f008545070400b410311b401c03900040079114950140e024503003401c89518201080c005404c001001c2522051301030881c401c80c1c403000034001c50503400703107410303150320b55043c01100c68196440c0c05040d16864283d904540c64004c0c46006240807990400106a0719044405468901407103c51358030300c0d40c0b20704c4050b5040101c201a0700007055051050a10444901c2c0002d41e5900d48041009003031055003810910035440c10074158013040001070700c00310420580c1130102c503a904c1503141501d08600a00741c542541302c0e14015640003d00200c840800143e40802e881400079420a103150048684480100262441c401001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 915330269 1250 915329019 915329021
    0x130f0e0d080108151305161a0703090b0a03230703110703050a0c0c08010915060b0a05030109020307031116060b0607030f08040c091d07050303090312030405030405061c06090e0c04 79
    0xb070402090028148441c1042d600c0e00d06201f61014800c0705150104410005100c45105060780750001d00e000d289007419541d4058020034940c06112400080850400d442034003d51000c115041c194100c1c008558400248825415003280c0c6940060706114008810541d55000d1304c2100d03031315441d13143c20000e80c04030448180c04085c1041d03905040c000d0001174a00e1080c070405002c580506c5035103001902c015240421b0340c00030340c0a224a20f000b0010a440c4a50200a40707056030017044026980c0d446401045015126101d400f600e40c080000d0400c0b546010b0440e070001442c490a014484014890200030b107501500c2c80240c0030038400c215600119103d1041a90702611400ca0350100a80318024242100e403030321010741000740c4191002c02d803200300300104001000700718019441d044511000c0b81d00e84103c0341030707652001808400700702084814400d42d005090098069030710383c80740d2041d07000c206810804403150a03150903004181401c16014080605440800400d403640400b01804 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 915331519 1250 915330269 915330271
    0xa05091018020421052803030b030a02060406050d06050d0c050105030405120c0d0806060712050a090801110a12060501020309060d09020a08060619060c030e130f0e0d08010815 77
    0x101071140d0811001c10702680002d06010481a0107000c42c01080e210300e816881c001c91060310000e01c186144001c0c060b4039442d111407800350b0f498580400c402100d00d0100c1c0c649568190000d50245000c00c002c00c8007503000000e00700710320542d0024460181d9410a000304445081c0d00501800a650390900007075000b00010354000340b01c0d9044484030a6441c0c0c090301250405e00c0059040d4000000d0206d0140d880140203400c01c02c00c445942ca442e842ea540c0c0c04481e484108103200f4050040b0700010614045d180090013820801c000b88a135404181c5540581d600c122000808901841c00650700045c2c2881201c06541c0c068005515100d10b0900f000341e0394118184820010391211011401a00c0700040d40e0018a0306000804945c20728104021380d0a22010303000d20360030400807041104a50054090f010103800d0306021900385c441001081040840380f0702e00c8040c0d814800324000502c078561080000140c0d4405a8a206140c1c4104458a840c00c0c403030a101540309200c4418010000c880711 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 915332769 1250 915331519 915331559
    0xa05031e0109020405010306050402120a0902031501270c0207061b050111040302100503090a12090b1615111b0f10051608040f0f0c0b180a050910 64
    0x491011500c91820351140402608000b1040b0f0b0007050030803440d41c15001d9200944011101541401c854656402c0704590041c0600c10003911802c0174405d644050240505d900c111004103482c03981c45160107201980c400380c256103988030b8014100c910062901c6904041d06203917004d040d0720741c94140110390700c1d115014142507000e07403841c091f80000c0c4d092294140141100010a407164558010007085070b03804680c07282844010010800309540215030761044951001269080d0b48071843c040301c084503550002a0034150010302e100740c030b2a0702500464a60704c01c10540c03481c3c009802d9100107640c1d411100015220081c04170704035420408108040c0b0014807401c5a01030101d11078400d20780784103202441541c81c3e0300d07400d1082151040c2e0100b08000d80c1424000d0a504240d5550090100032910140c4a1028030a144040100391031140c0020100040d00301d031241000700300d03040c2110120285502c03e4074007020010341800d0140b411441441421215041d40c0d280641041d079040c1a0386903 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 915334019 1250 915332769 915332791
    0x20619030e030d091e1212090f0b1005100212070f0b07050421080403031b0606061106010801380a0303050c011d10020a09030506180d0809030a0503 65
    0x901c00d66500c00c0016064500c0141008100100d150034010000d1a1100005a00c5010a8103510220740d03003140b9400103083e10320304500710098882c1008003c01c903510004041c40c5030708200c072086c0710122001e20f0003004001040b52206a60304100010100b00200b450050b810034402c40d80c82000c00c0b000362045070300a61480441841542d24010014801c8038a00082a40031509102075241488403440c0c0c0e440350030b08040100b0143d00c03058424000c13444014100300409420341c4c120440d800806410b070703074426414172500f6200c22025020780d040e89002040e038031426000050504050080d001e04148440030100000402032a80c20500700e02049001103000c0039a148045031101d030324600086000391346150b00d5243c00385040d429100c1c0610007201191441c2c01d4201e115401246084014024140061351050714030410744010b90710303900c054018054a070030040716480d9070700d00141510004068441901403940b003901e60701010f44000016520600041c4100c2c0d000f0300c01140c2003020151303 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 915335269 1250 915334019 915334031
    0x2401030c050f030c040e0c0f040b070602091e01020c1f0c0f0b0a020711100e1c061415091003200d0302010e1018061116030206010509060d02061903 65
    0x14240342650f009031607082c450040040c0401c009039002d02c510742c000741c0044c00c5910b0004100207400316405140964215070500244100412403154100d4183c1e80c1c0c003411601c440c4014141d81c1800200f170206240c00b50140030310110092a01d1f00c25600a81202a140d4980c000042d00c00ca0380222aa60704031611207c6010200114444810451090818220240c2c2e12100340c9050030141c500d00d04e1040c000e58600044402d0240c11215540480d2426250100440b29800c180501e410f0031090181c040b5140440d1754880840340c010305441014154800c840501244050100980303003150342019000002e40c09000041c1074103d1260402000040d82c40881d5640000076109208040102d003d40e40d917449188404000f401000301000340460304012080089004017191007946100502160340e49000480c1e2a000b44282e403a80c105074180000700d01d03154a8041c2d65510207014032791203101c0c1070001488030b01c0c1001c0f101120300e90180040c1e080500b01142207440441c0030728020141522a4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 915336519 1250 915335269 915335287
    0x3030c070611070c05031c02031e130b0702090c090603040f030903021c0605090706021e01060e27070506090405070207031b06080f010f0b030a1103100602062401030c05 74
    0x42c0078003502d034002c4030510900ca180408261401220013081c04110102c0c0808801c140c3d008025920703ca407030f001e0405450140040c01009901c1f401d4003901042710010307000b00d2281c25100160036414400c0e102d141040d03c5003054102c06006225519034800c00800c00600015035070030b0f003201e503107100341045002984c483d80042c00890784000200010550404030100780701e15400703100e812a41010207000c1032070070080000d490300700030201c1c03000b056201421100d00751001d40c841801020a03a5610310103041c80580044220b220840d0f510100c0403100a0000558001c42c0301c00c2100d00003420300e8505113480d81880080c010041500303066008544000000c1031002001c80203e05801e22000c4455061100260000402a090320811600c240050102100a0007064180c4030404c054540f665903100d101c04c050a01c54907800e00c1070b580403080c0302d10505005510710580c2e141741c007516007a64034010003204044445010381d0f60184550300c640841d5009901c141c1c24900e0501d01306e80781030085 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 915337769 1250 915336519 915336551
    0x3060204120302010c03060602121c0f050402132918010303120606080402131d0d02070501080f0708060f0406030501140a06060c0305032809060507030b0402070503030c0706 76
    0x660103641110107040c045010154284905484108a41020043d085c14540000d6035942e9881d02d403501508001600006c5a0300800250070000c240101030009007100e409500242c034060360308074001d028490038680300b0800c4d409004410701d41100704044a40c1c56910281d0f800480081d065040300181d66684090054104150701860103034842072400000080004100c4590758407807010012000c05110050351252141807409003405408100084800c8120103a5800800c415006100c0c40429410132900840e0500c00c640d000d0b00c6803942940c6400441c046400d0840d498030020305003600040d603a00e0502210254400d0140c00020301540300e0b580c0c0ca00312141c98184411280c5580b00b04020060103020f00c80241401b40b0340a41c0503c090703500584140009002425102d02e0b0382905c05956260140708028000124821f0003801360300c1c2885030003400180c07007410000c3c3c20034540014908060080f00c9085034030100462865031a6640e8a200e90015001100c109803a1b1001a0460000e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 915339019 1250 915337769 915337777
    0xb0909060708010b070816050c03061305060a060605090d0c0f170d0f020a0f06090b0a05090f01050105010504030b0901060b0c30040302010e0a080d1706030a050c19030602 75
    0x52180201558104940301402400050340821a40c01040182c9400a0160000d440c0c450601000004a55420b4a041c50800c421804100d4143c81a5010007a004a000d8a800620b5010f40c0c00d441d500e8495802002c2512030394001d0002065013004007074100d00b465030118890900921554441d10f445240103040c40b060390340b100b0042000c0d00d0a00720041801d00c540c1034848010304080420510166003c1d481e0104c0b81400741c15181800d02400511542c2d0308003d031020b0b4403120205107480c10b00e40e01c030010712055428030818496003d0b0b82810308414070070141a0307101611024106855691803d0f40014000c0c4514070f02c1d501c40c0030020352001102d0281840340800e5001c4c101c0300c09165102c0280f11000d11002c0f0840c15901c5044003820312240403103043d0303038080c40c00d601c200013030b800422203c080c1030740034041c14851070140e40604c8d03911040c0c40c522031010300340380441ea807104803c059035007204000282013500040c01e000c0c2a0310b00b446802c60030061192012222603a039032500c00880e00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 915340269 1250 915339019 915339031
    0xc100f0203220614090c1203030618040c0305190302010f0b03030d020724090201080a060522090b0a20120718120623040b0601230c250e07080a0b09 65
    0xc484c6e000c1044c02e28014602c030011070400b4000f141540782004c0041e03030001c5000700a44840d001c0c1000308060140c565030351000f9540120864045011074144203144196021042d0019440d0007000c840c1e2a06502482e032412800030700031418202e0ba900c0d048001c0d801244100c6001085003540401c40184410303203080e810750b0b00c100041d1003159000140482c0b41c0100314445091034200103210170f0351410155000d0010302400450508090032a4000524840760050300080200d02044513030031198001000d4102c04904e904030320750101d4482c00860081881078810a4400382c009150240300c2c1030b9000804000c1c0c850b02e141d03559503103004501c3c6e0b21461029036100e51a0700c1045460ba42140300030b17500300c2c10951044600d2030142c85501d0741c214044d140a0401003a458003121741d002c5090440d0300c5080030007009035245240904140c2e5403900100d01481100784c00712500100d100c403207801c01118003e80110141d692181803c988086004103403103c116070b6182d402465807a82d4448030300c140 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 915341519 1250 915340269 915340273
    0x90c030105040c050f03131a1510140702090703110a08010e0708040218040203010f1a03100b0a0909021f11100b1e0a0b0c100f020322061409 62
    0x5418030040c00160f44810030a1003c0c0318040019405810341101225404120042044181142c0d890200ca0358507501191121043d60a0180302d0380314103035000a2215a8121200c2c80d201100110035210f40416070380c5611005003c1c07140c070025041002081d64402c102d8034002401c4c024003c2d415945800c2542403c0000b10148014000b4038100ba12140d04054503040c10300c92840d15500240300b14030445070110032101c00d440071400315202508100308081220005000c6a003c81020004076001007030200c0c424031035100c07996050022482611840d80740600207880310380c246184100138041c0884202d0f08407440c01c45803080c45da9030340e9000c00742484a40d00d100c101d043d01c8031224907088603c1003000000c0d20740862200c0c2903960800e41074581142c40064611040143c0c0084d50640303003a84506a22400000c20268080e401300e02a40d211040b07040c2000704020f1012002d089000468039026544983d0494100682c0e41209062800d4894040414102a41012403445d42c4041d41c450741e4503 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 915342769 1250 915341519 915341521
    0x204080a0605061804120306050a060f0201110304110d1a0f01050f2e12181b0f050d050f0d03060f0b03100920040f03020a0b0a0e100c02090c03 63
    0x4541070080c640c1141c0c00320b4550a904440d0207004c0305078100035000501102c1c81005030f03180103009070003100c0102001080400403607610500545665000c0b21030341c0041d407138004903034041c0c5404401d90b0b0059800c00640440101003d060244090018200f0350710540944072600c803032013203844840e104900603481d000b0a94549001d00407a840f80300a001c0c8101000d0f008110f50120021f44411040100044512a517a400400303a59010f03a894900100504141100721240c842011030b44e07001b031180d198040c0034001c50804002030000360062200d40711190000f0009854a44210150503001d042603624041c864600240b500007000000c0d008aa1980c0c0c040141d6082204001c2c001c24005111510b549080034089841c462580200c1404a42e2111a1803490144039142c90342d03290441c0c03000c0d54454030b50b0000c02c0216024802248100b84114002c644080c0300300c241d5122002d50f407107150021b81c49004001c2058400c03401d41040000c0380361a040540d4500d81c1060107100804c4805a407 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 915344019 1250 915342769 915342773
    0x7121403160b01060203120604051005030f0609160f0e07120203101404020a021011090a03110a06090e06130b0612150109240302040b2802011815020d0204080a 70
    0xc02e12059111405540051200701c000412061303956034004802c82c2c000485565a18105188c00c0707040d00800d40520801c1c03542d503212540091064000c5050a00721049030f20b180e80da1800b12401f6004407907004611b03681c10405103003000b0006812032100e00f48030707403140114482d100490f0800c035101108001005020442c07100c5000c2d5007500d6007000c2d941546000d01c0510040e5a0384600f4a008a0307160b03559161400003080841907907c80540101440005d5981e802c02030891000b8025203441007420800015031a401a44207400b2200444001c3c07102e540c406081110001300c0700040702c0f059807100c0041040d80d0b545c0c0c0007004101d041d00103014080c10001d40e8880095410000d45042c09145101440303c00a4084505405c0045010b5159100c100d20380440103406107a11410000302c0201d001c101d0711034510720002582194400c07503010404941030890aa440031811850354451610314000440c01400c3e04c0603802c1c00710480949800c3c0681d1200c4103d0780076138005c1c4402d81000010800b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 915345269 1250 915344019 915344033
    0x240207030f0909020a050f131703120c03040201140c0a1b0609050a051828060e0a2d0212011202090c0316080703140f0601110601080712140316 63
    0x9406040000c5082c005c00c00c030050403030310070001082e4001001048108400041101400c01f0300340540840510760000c41a4540e0390f00500d2040c400303807c2c60000503103989144001e80388a00c0d0142d554071514a03071002c044826901a100c04811802030300791410100701c0e200008203c40102c81c40703100c113041c94044000c00c803104503001503104d442c010208201035a03a0f984075443e00038241004c003503075482c0c025400b815403d20101d0203040c1001d40300040c868240660002c800c076403108501856070350350600d01508441c010100500005030005501100344d0b44418144405408442c006140c4102c46d000d580c000c40b02603000715510400b807200a421400d0403c94a5004000c00c0e00490841c2800509031030454414040c00d400c00c002c0740009006144a07400c5400d03800d0a00c0c1c603001c82420b0076503400540c0c1d0ba088400c2c03400301e130700030501c030303180e4440002c000c0e048400e0b9001402600e41880005111002c1120b81030310544d80c2422035540101d8280000e001000f801411110900e03d01c1c50041 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 915346519 1250 915345269 915345287
    0x2042004080c0925023406020f0a031b020619030b01050a0504060c030c081b011b02070308030402030111030708040309050916121d01050411040506010c240207030f 72
    0xf4001c141840921080d0315003080301d0006070700c000092003980020020b089180ca440040310b95100b40c0c80c00c2000101c9103242500c08414600b0030440380d00307240c41301401c1e42c0d198681014117801d9400780f03c0c4480401c0c890a0808688489801c12a2040c66150001903542d041346243c4c42c40c01e03031a4003c13688041d415114180d43c008080c28410700300310b50b00c0c001404601441c85160148030b82e84140368105403240901482c82544840019150b60b03200c43d18200c00c49207004000543e40c03030801a011560103650f20311030b101003140d0044c4041411660b4400d090b400141c0100d030190b4903940da20401010b40006107204823169602e0148d14549801d0081c00340d20f01d503101c20b014001940034401d0518000c0b130003140880c4c1034200a0a06880c550048004240352070800e030b0448414400c52200e0201900428055402800d024041c200c1002c00c0008588040da400c0b404560b0f03540d10800021100070380c1440c1503400304d03400140d0405801002060368040001280010354400c40344110300d41210400c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 915347769 1250 915346519 915346543
    0x100201181109160504060509040605040e060402030c060c070b090d06020403050f1005010e0f070e09090307060f0c0806010807022a040c0801050f13020702030d0903050d02060606160204200408 84
    0xc2c4240c80582e00007a00901c1746024140401400141040d40f540380ca8001d03d0007404050010030440140856158a1300c03421344c3d04074401d0281c041444501e01e0140c05503030015000c070000d003008500c0d101c16030920f50700c44104241c02203081005000071071000c1c40540011806580a403100d0007a4907a1641000b207907030b001041b914941001800500843c800c610f038040b8100010808a456200c4156400350080b0302442d03002885800300002d883c1f002c0b02130000c4c00d100e05414440342c0780300240c0fa03082d910b2178010403001070000380005038190302c01e0b52001e411940c03600543d49100400f14403200040345502600380c0d50322013880460360a00f024800c1a20300744c00f92800c4c0051394100b00000e41d040c1b8181d44c5035485642200d6804a5040c001da0481ba5225030080c00c542d0306000c3d601014101c0d03001d074401030b03c443c050134a20ba0940c90020480500c507180c02400d1601e808500403100391501b08c00003042c1e070006d60310110300380042201c0000d0102d006440700101e86941c80d01e000b00307107800b8450b41c03c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 915349019 1250 915347769 915347791
    0x20a0b30010f0b12270a031101062405031f030302030403140f0c0f03011d010e120711060d0e0105041110020d050d05150a030f02040b04090809100201181109 69
    0x40d00c50310320400c1951303d401c0380c500f8030580090f6482d42580c459110005446544c5c90140c49a0002019000b1101c243c04020343c600a20032155103145900e000e0038500c0c8410f00c4c00d20030b42c40410b0b020317104d14000c55110110105480e60a00200f288100460301354008802503800000e007441845101d06140d07501300552801000c03164a41042580c41e10004180e40d40203d0942440c204a9502904021149040d15000e40d04000700408441e02820150b07401804070b024004607001010700900494030025004000c10306150384480c00d10540340e0242068002d001d948050308030f202a004e020b076900130360107400c1c84210101694200a203c0729040710f51000e643c00b20580041188d0444252804400140400101d5968100800084035009006542d100b0314805000c41044440079041c0c5d4218000d64041000444190a000841d044404040d2040c4420300240c4003034500018040302c41b03241880085440c01403207440f000300c40c0540b101141c00c502072180040150034030344455548080340d251 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 915350269 1250 915349019 915349027
    0x70602070918050a0b06011e0207140301060f2c011d0c04180506030c030d0801090e03090904060e0f0d05090f040504030f0c030221071e020a0b30010f0b 67
    0x6140313662140714460082402400f4000030b6042d86c0160b04d01c08040c280c0d09100c07541035500840094642040c1d024100c1c1c814110f401c1d89060782014419501a1002040c007000c03824100304900040714203018050068001200c0d020403000d210001041c0204041003a44c0c0c0c0980245200084041d0000c116401060342400104000408030f10200e03904c0511840001d8140c0382c0384007290800d2002c3c100a601072040300030740d5001035481a45a070495001450400c50a00b4044445480703100324014150300c011601c0c0820082001907111200c0c0c01c18410031219010320302c111680c20040240001c10128001196100641c00c00707000d22402804100c8080003603103050399001c1c044c00d210303403100801c1258410307004041600030803c195481001d15107642d00101c02d804120714aa220710821144944444035410883c4881c0b00b1844445d54002d0000d101c190901c21803074a150008020501e040c0c0c1400c6039203405040c1409841c0742c0c071140c001c400145604218010341d80c406035130701140051400300 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 915351519 1250 915350269 915350273
    0x110c12060a020906070c0305030901110a050a0b1801050c1b06130f0f0f0b0a0b010c210311030907060810060519030b060c0105162c0301020705070602070918 69
    0x41145540076103031590050b00d4241c0e40010880768041c112005000d0540e101010017400400406000501000d03079a5515034014094010344642040500909551010300580c0008031800b00701070380081300741c8030203030705021844031103082d00c90960315980729680001c2c14501f90300f222211802266103241c011b20407424424500d00701004200e501402040500f6103130b4040180403040010402d03040300c00c040a1070610700300441d00f00703401d5404401c40703803030318a00c82e205500a007001141a90489005106543c2540d4007103025480b4000400405564004c0c030701c1280302407000346024080c501d004103001c07414228050038204011b40160444000b540301000714070382c48400c4910051440348a9548050818000d401400c80365294562003840032032650140141548080d10401003031101d10305a851120342500c00410028150f107480c0d84102d110802c522119a4030119030101400041c540491605c0300c07810b110a80e0040740041c1c0000f802080903041502900c410b440e814045102540c90039 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 915352769 1250 915351519 915351523
    0x110910030c080d14030411061306030615080a0905071505130b0f0301031b0e0f061008070c020603040c030c080a0c0605042706031e0c1d061c08040303110c12 69
    0x180c1d96000300c07084d0000000d4200b00e07095051005440e0050141900c81810002c1041d2041a5004110000340b61040000d900f006404507420084032b50303100c40906031214040a8043c0c42d40c03540c2901d951040100c00144107810500304280c03070b201a91099140c110164681c1303001380e61035010075820642408041c18075209030007181d04490384800004110b01d0290381d0b40340101c0710342d8007032500300710000100030070441c08400c014400c4008541030310903040b2400064800c410203484240c0010f881c600340360010304101d00103540140c0104c1c0c4281a89540e40c0e14401458019040240e40d0340207444900204044101c410010340601c0c24030506013801c081c00172010802543c41c541540308000b10510380c0b024140d020001840d00100490203000e41140e4050084d052103004036004080a0b500180d030313681020303402020401c003200c1041c16032208820001408607244000209032130b240095000204c0c2400100300440c8280ca54000c416081d801d000d0601c01850b030101d000d100740300b401010b21400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 915354019 1250 915352769 915352787
    0xc0117061c060609020a0507110a060516020a030206030a0e0d1704030528030b0a0b252102070302010e06210901020705031b0111040f0b0304110910030c080d 69
    0x241000c18400e9a000d04141000e01500e070701038404d0610000e0590411903203e80209800c60244000e81845e840400034442505203601c1510006038040c0a400ca0520b4200c071640710860000300b0300405030b500ea0700020150761003a104004103550307500e405d0f080c0a20511a4051400309820f100400a4010f0305030401550014401800c1001c002010414165035421645003450090b1600ca80d0801c0c00710040c00405501c0c003050301c14020300c0c200042281104044581000300c07940303020101c001c1c0311090100d68036054403c842c1c00c100c800001040781000c558440b140c0d90a6030041011720b240d400090064207008440c079000300301c00c001c600c1d40c3c00d0102d2107800710340101043c1c0d421a03507a1150418024010f1004c01090340c00300180c0100c02070306115810130b5002c2094000c000c840d0100528030541e02c03d40c4030f00808001009030821614111f032000d0760b8080d018224000c0d280700b414002400070f4204594111500210501c01c0c42031200ca01010400744c06003400420368500740c403c01800c100c03c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 915355269 1250 915354019 915354049
    0x302070603091a1009051f0506210c031009050112030804061509090605060109121704051503070e04020f091c081c1b0e061b030c0c011706 61
    0x80c032a02c211042080100003c840307150304402e20400c0c1e0401c400c0040c02c14805218412203181081e0100d22016034007242c5900300322024200d17500c01c034542000d00046401c82c030181c0380f040e01c0d502d580c0c1e0340d5660100720641c0306910507130f21107a481c6802030341d0040000c0c15800c030360303206842c01c0018402e524081c142901e0041d098188203070584c2e10361074030b0350142a142c2c070443d0001c4205400003504285581050503d644105810300283d0340d01c100440d4546151300c0303504500400c00c80208040742c9846d8406002e100b100390420301e49904c410116421002c0c03c00040c0840000004000da03103035008080c02014901103500b0b520f4007140c1d41c040e80881c020b484002c0c1c4070b1103024408110144549400001e079503030054069407917401010340d820b07481451146103442281041d90340714460004a804901a00d216203c89100960000912444c0c0d00a25007203964201c401002c0d8040700b004101400b521044c1000500003c04000001402c145075040c1c40c3c0d2030070001030f05028040e9654180e04d49124 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 915356519 1250 915355269 915355271
    0x1090206040b1e1c23010b0a03110f1c0c08220f050706020d1110110c1c020d03110a0c02220501051507030e0108090111030c0405011b0302070603 64
    0x281000b01c1c0004a00241c0355080c0541c02c0084c100d0b04e441242442c40c1010482010108407500e00740240b0000040c81004c40c00c0580c91103001030101c0a400c00282500d00e413070345000980c0e60341e0901c04c402954480d401c56000352601141048100b003400e410708201200400d030900510850381c10140401d80080c184070002110b400000f0b10040040c0e409011458200300101422003035030030603544805941c02880010301170401030301c102d02d02811401415003040741c014103446032140310ba00002e00305001c20740e0340ba100130407101101220170010381214040a1211300c0c002802c1c044003a01c0c041d0541c0c280420306081c00c2c1c501007219070399800e0311600081803c1140505c1c10600c0051009903040030450604a08040c40c1180344081c4e40c03010341030b00c0c4c0c10340381c01c1000d080310f030b80340607041c011a007004001500c0091411181d5120388042500800750700c00102e07040480b0001005507400480e031028030f40c0c0c0e01003010000f03980c0c802d02c03041203012001a00119074166480003034443c0d0300b90040e0801d00d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 915357769 1250 915356519 915356527
    0x30a030f03020c060103060b0a05060a05090607020a0312021015030201020c0411070b0f010302030601050409261306030b0a14011409061303060f24030b0603030c0303010e041401090206040b 83
    0x2140039404440c1c100b4040070a44c1c6140da101c0c03500c2c4000b048540106030086065070800320f80307810b10324100c031032030420ba031200c0e0f09110415040000d254400d07901244c201180b03903030020010704a1464200903900b0781d00900316506140c5c0700d000489219451018500d21354650030005030b40c01042d91491048203940c04513400d001da8618442c42c2c850450000e0a01030418104a1003012605074281030b0381c42181960a00d03680c031020401902d00000d0080c2607000351000900a450198078040700b0700350b448154074185206841d901d002d000681d400305001c00c1d103412040f070031450060301c00c0380901141a480580011100c0c0000c0c58401c803907030241c2e901c40c400103951080e17954a1064550b0801403204005a1903240e10300203000d44603008001800f14240504202c400c03540ca540c40a480c0d181d004040c20082c51500c0721010048054046505800304010428108005000440c0a0108940d0b070036800d00741841c0510b2032481c02031400c0c0990340f410410300016070300c42e800c90f011900f1083c1540e8071 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 915359019 1250 915357769 915357797
    0xc0917070816081006030213050403170c12160c03081b04240804080a0e0f031b03101e0c210b01110f03030c0319050c27030a03 56
    0x1800c506a00406000c0c815001816031030003201112409a488410665824016110b14201a61a01d020080d031102e032005003030352904100c1d80000e600038064030780740f2941401c600960024000646441c0004000042d488410450b1a50345607048450302d0024000c02541c980c0003801d0041d0001c2c010204116800428401c4070303d10410354501440003541c1d0b070f4031707540c540d04880032402644002008016541000a5150003202e10741d02c11600a100d503440c01c0c2420004849035815003d9055118640d41146401510104079441c6c1c0c07007001c40ca0180c40c4c00b5054041515041101c10300b01003050401600741c0410a00440000c02010703031034808100c4105020055130303004035103083e48401c28002250440b400c201c540001c6c64656007a01c0c2d0a00b4004003a03403c1d40c44002c0307203042c00815842040400c00b40c417280d034003c51740000701e8040d0f141c6a501c1e5010f041c080c0ca406a90f80d24000c4004100c4041d66036030045d49030b050048409004282d0000c070303800310303859078071603480a000e210441211f801 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 915360269 1250 915359019 915359023
    0x60609060d1b0e010e0906060a060f27090b0d052d1f150506030115030914060103170c15270703050f01050709031113020706020910030c0917 62
    0x1141c00b405009054005071164002078100e41e09110304407034a04a1004941425000300b910b40c003400000d001c0b07894650420341c0030390700b00d400600f0010800c40801141d80c034113a40940c40f40503001161522107061403030300d01c020081e40d04828100d8495000480000c0c00501d0008491000c078000302007201a12001d40008602d003281c12080c5280783c000c9803c1d5100501841c610380c5400c0300601020401c030200c0c4401080d0762122401041d4000f01c040005010b068080750507144400403a2a0100750300309580e0302c548031b80b01605440c0c202075200c24010720400510300891000064111252824902d0001a00d40e84240007113021400d201d0800201d01c40a04d20411500380c0c00310b0b1403840c83d95030040500d6964600e45480281c0307450003244035500010b03006000702c50003509140e840012880c02c6440380009c41032841c1c0459405010080c840c0f520f0b076030b14000b61640d1340c040c07040103031110100404d2000f1031460231440740405103042c502074212a0407c09440981d00c0d0f0b08540c021040c0c81240141c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 915361519 1250 915360269 915360293
    0x30f011a0406260a080a050307030501060503190e330708040b060609010e0a290c060f18120306131514010c060e0a030908010209010801030807050c09101502060609060d 74
    0x5e044c205001403034005698000d0300860103210b055404104c5aa07848908a80c540015204248588400782c0d16070480d007030703a4021909002886003a074602c1c11000c0e506848154080b0400070001940c0d43d0b003c041081c02c2500580d01900e5420101c00d5450f0969500b42049030052409100d10710105c0c4144c40e40c2d210b94520039012402825040c0c40680355100081c1160300d08808071040c100381c45a00c0e4501645405a5004d000d001c801489943c0b00c440b10b00b491150000e01c5c0c2d0640380c91798040000902ca0801900201403200c2c1c000a60701e0404505101c840d800044031458a681005030001d600c07182110b60008580302d5651a0a400c8107200040f20742c0a00c044000e00050300301060305803070000200e81d10381d40d10310944403500500c1d5201007050a0380a160710b183c1c085024003004202040240d0b0003406828030034416150202c030000c00080a152040c2c42540c1d895590100c00c4c00300e910410380c4503109a9035400100110b18210303000031066030005050301c0c014400b4560000c00c1049007082a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 915362769 1250 915361519 915361523
    0x7080706060b03011403010e0a03030b03030d0c050a0e030d140a05070203060907151107031506230112060e0606090f0307090c020d0c03051e09030f011a0406260a 71
    0x3403001550b500c0b200021a0000e001d2035003104045092805145014407480c4c0d818401c40002c1d040c62800c0f501d0035001801c043d016550140002c0100e048418502d1040440600305a1140d6403a001009002170040440310341803030299006102c0503001c590004610081d101c0003041091b590030a4400c102c40901510794000e4051090740140f04c0c0e01d2070086024003c2c0c80c0080c85003400d01d50000802c40c3c0c201c000c00c650300b0554010120500100300070f0701254041c0e00c0f000c5000b00d007195950003405400c100e4812108050700001c0510b082d83c1d0f0b48070140d6180700c0c8a0180510110703041600b00752919101601c0644a650000740400050300c80a4190155070002015503880565038100800503000c00c146110040c0501c2068103c01d50080c12508852074060307a581d0f06007c881f080a64011004c01142160810103000444965500308500050f14401c1000030170201c00d01d0151040c7c081d844036004e44500d040c00e6042c021403500034500000018166041d0501518a28625042c07902030600 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 915364019 1250 915362769 915362771
    0x6050a03050f0105061f0f0216120308010b03190f0e0102160308010f03120503090a0b01120204050114092205100209120a030e060c25181b030207080706 67
    0x400030a0110216015549040c968001d101c1d940d680303010468403c1000c8074501d080c2c07000c40c0115001038482c1c00300c094846802d0049550313041907909403a003650141d60026000c1c0040011140826900a0169005001589101c1c0c118141b0004000c207a03581401c807800001c0d43c3f20010601c48140f90424410b030940113008554400a1001424254036444001c0c0c000c02e00d2030000084c4045040301980803650445a03202600d24200c104980c3c0781e0004e032040b1850312940a640001c84c10194105000f4076a403098101752423554810b00c01600e6059000032507951a40c604071421b40c503581880d90740b150700060710310f0511b1070016440c00b071076100c0c52016200e4880c50141007040d44469004100b603550850740d0300030703503203c20040c40c2c0d0711444104002d0000d141100350200d203003840005420203050310806d03208000c041c1c15208140c1c8680002c60074204a90329801c0000703044403000404d252003d000305100018040400350802440200d00c402050780c0080c4080c2803020a0040d01c1140d0b6102c1c034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 915365269 1250 915364019 915364039
    0x310090309092c030c1911060d0f11040602120414010c03050706060b070309090b01120b061b03250506192703020c0103091e0c1710060b0306180a0605 66
    0xc940781c0c0e207400041c3d41800030700c101c1c2c20b91004400c00352206d52a0b298032000303003078801055005000c1240c00c00841100d0003520358001e82007d000328021224041d03014004141c440d032038900c4c02850400380700c0c80b43c440c1420402052042c1d810022100034011001e01b41500d0115842c50100c4181c4104000609014507121002c82c04080030401040c850b03000380d580ea1485a00c50000c1001c8541d101035a501041034406501070031001c540100c06041402841306080c45d41c086040701580035400368103c41e58000084c855010321004524003130095150b54000d00c01d10469407901e5682c2c00c054110000d2909460000031001010b4210b5036820b0b00c1406400010700407a616805a03020080c0110013502a00b0400103c55120348981520b42d5000081640c1040e1049544c8400c0d103c12241950f80300c45000001c242001d40d0046100441480b20040a40b00c082c428450200c0c1d21b95003024030040010824072042e0307035802a000c10b416804440801543e103440090000501aa40c802d54104500e41c07 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 915366519 1250 915365269 915365351
    0xc1b2d0c0807060f03020406021f0213030305090901090b0102030a030216120825050a030f1104120506060603040305030604020a030b09010b04091104080304120303060b1206031009030909 82
    0x403a0601c100c43c00c5454401c154594180103509900a41c0100700042c1d000140780c00c0303000344260343c401202400da0300051074020080c08505440d486500143c020801c0040e01078041d0070000002c900414a0000404c41c010003000001c1d01ca11030881c042e010141c010070002c2c11784410b0b81c3c14100090380550074103194081900d02403c5410202c82c905044403041c90105900c2850943d074030025002591504d103040c206500a80080c2400d5401b403800c0c0da80c55007810790802100c802000605040c503028206040e40d441c0c000d00d0032400400350b9005003410300034800040c0e00032040c3e81e00941c0c2103901503101d00c5540741c21002405a1710882da4003403031101c000a003e440820050040d5200908203001c09078400003812903d100d03070310580e078a560007040100100c66032003010072012882407802050440c4d49181000482d00140e040c1c1c0d2a406a900500c80e26150401ca840409566000b00303008070701d03c41e00c3c05404000b845c4143c05501d61500581010038522110381c480c5130b800164075000100440c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 915367769 1250 915366519 915366523
    0x11202090d030323070f050a031506020a05070b0a0c06020706021309020a030c09050a0e1b040807060306120b0a02030c0c0321061c062d0c1b2d0c08 65
    0xc4580601d0440140c2c0050959103640b4414805c10315a00c45009482d0207040c1228a5403010082c1c108156454103d803280901303501802c80241501d030700801e00104982086801c0c00203561007404424001c000b0050001c0d01710f20200407840d00130300700580310641400c0040103445a01181d00092101510110b41d201c0207078081c01210301c26560030054000006016641c000307040c091035500c08041c04080242a80c000d05065006210b1580d0f440c0d82c110b403c070f452680b9041078100c031126421495061102e01d906110b0200148089400c01c03810801c0c0741c5500018800242040c00e8040d00000014009001d8404640b8015040001c903952003085001640d0700da0014183e500310200180b020032800e107400844801c24410b000950100c4910a41e2500024040c204148500c5484004540b0100005046508100280b5100841e0100c640500181014206401c101800d1120f8800784003141349a41d0300d4000202b650004446065900f040410f00c0000200c014400c082640300031402d0000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 915369019 1250 915367769 915367781
    0x80a030c0908030c0c100309021e13020306130c0203040815040c12230c060c031e0f1602041416080106020d1b2307082a011202090d0303 60
    0x503a541d0003881e0300d07a4056902c0348903040750000c1e41d074881e100c070052920f00300c020103c00b0301e41410006a1100d441d4045404002c0610080e144801740c1554244141454402450a2206000110301e035141c4000002c80d142200a04100e04a82e100407901846008000700c0e809032004a003114446055440c0040848e0002c840449105001400004401801603004809079910002d140e500400741031200003410305803881d503405881880400c441d180c80340d00043c11080b9000380515a901025410800e0582a818560300d650804100009201c8a000240c03042180218848000907503c0d00009001e421030201d8408013804281c14080c0843c41441c10607075410321030315502c2050381e80340307800d1340c460400e10686030114a0024070640020f2401507120354180c80745540c2c2d1850040e03242030217012808003421504607401100d050001030401c1001c401d0803886807030261500c500e000c810070030b8212403d074002e0500c40c0601d0a03810241041d010389005203000303441c2460040c006d0074000c0c00307030030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 915370269 1250 915369019 915369041
    0x10e0f07090f150302011b020d03080a0507090b030a0f11130e0915010b0a2d0e030c0a0e07140d0501140105070507060807261602030a0206010b0702010903080a03 71
    0x85048850302c0c42e618a40203514480c9005007011014078915001901c1d100d40c024080e800300d448aa00c83c0005a03a89008000030768080c2d9280f44030392400d4000c501c101c5002130244400d202c0c4039902000032448041c1100d611200000021800302c2520ba00c010181c000ca0b20341c14015000403814002007a075514929044500307030a0f4181c0c0903181e01111507100c0d44454096180c06e0110030041c4a011019030007094030003100d1400303008900c0300c2d0078a0744074180e1076900603074800384840300d0800c000c2c0e12842150030308208402520340d10b104d417000103480c0710992044440c1841c8980000305124064800380c40c0d0150075501d1740d41e81d00300c2e1450800040000b402112003044003030009083c9035224109661002d58010001c0c15410300b4124107844940c0c1c01440001000510059482c851084e48200b0b07014050240002ca014200075000e1040122609070b04400c40d4010702070541c0300e40d4001806811a111400201d40c0c80845000403110514203400107403011800062020b403c9901d82d100e100c1c940 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 915371519 1250 915370269 915370271
    0x130c26061e01170606060f191106060102011404140c032e0b03030904051b0d0212010824190507020c030601050a1202090a0212040b04030210051017010e0f0709 70
    0xaa00e42ca2508030700460982d504a0607130084002400d6424000c00a0595400d022503060070217812070801469070b414844c031394000034020410078048a00c00c105894101001740002c0c050041d180c0901e05030010b004101511102c01144000c04a620610611007904006026105d9805141d00c05421008640d07440c20307214680300c00d6510880340e840c401c3c00c00c012401400303036142c03040000c01c01c0050316001c2d10080207074180b03280031031440e50706900a29001c18100805a120001203440c4550100305070700820f401d0700311130f80d040c1e400c040541c4940d800c041e00b4000100c194696075050146001c20718221000701d40b62200340a440b6800041d50140c104084048524507a00d80e014084060354030b110300c1142841c071254040c01450004101580418021001400d1800118094224040581d000c0c1c41d80e401510138082450b070b06008c0c3c828030400154040c1f140b8141480b1140c40525a4031904a80b0036032501c40316007c02c003e4102240b080081002c0324554080f041c0342036141d4909126108000e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 915372769 1250 915371519 915371521
    0xa030806130908030906072f100515040e030403020d0f06020409020d02091c051002160602120115050c0a030e03010b0301090528080307180807120605130c26061e 71
    0x11445414074230240c0d4048035803036558140d07158400b01403241c2d50304124031307078012480e0b08082c1c10307803d101e800c3c03081094046110740383c01c1120a1100305d030084000d40015810400050001da210407540c0800d082d4001400c4402a056003080c1000b405250041800c49000254110107022a50050a10306104540c000b608440f0340c41e45c0715000307800d15402401ca030801001000c3c11a5254042c0011a0810001c00c2c070305480c0783c1d240c0d800caa025010f0712501000d00c0d030061010340c00400800d01010f80c503040041c90030240f56003083d43c0d0f035038481000b41040358418100303126031020340142c169402c003d0002e00100c1c1d2645001030300c500d60030400700500350340301000d0980d05080100409601b0b404c4840d15195480d0040115402000d04a420403042a03008000420701c00800000000307001100400c1400800d5180100c25902c0103840d0583c038100411040300440c190b40203020890b5000040d03102101c1c1d580417100c8000341200c1307000400340507500c10050454221080c4002a441100c1758800c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 915374019 1250 915372769 915372781
    0x1060806040b090403142b0504060e0601060207030605060d14060103110609060301090e1510060806152a0a030c051612080a0507080d0b0a0501030e0a030806130908030906 75
    0x202c00e04480c0a030000c0c0300304086851804c549402801e0b8458040c10020781c91440300e010411f810703000200d00f160941e650003080140640e0b8440d43c918541c50001508035940740c081e000b0b503184042e01004d0900b81d6a4400b207866503442c20512521a03034000018128030304610041d43d05c81200b4030013550707074840a112001e5545050406c840480000a01d424116400c2248903401403100004048049c0315401c01c907014640307026042031088180402c10b4991070300784407000b41410000f9201c00d000e1005141c8242c082d0907150140e0301c091000c8084c01400e0000c035400c60030f180f201300d61001c00601030440000306140e84422640c0c1c440c2c0c0698100c84120741d00c0c0c1c4142481140600c20f1480401000404d14006a40c80c40140b4007042c0380d01c0e101c4d06107103060300c03840e0555000101109102e40ea07581c5101e09801c7c010215001030409007010460401c005016907191105400014108110400000c2c1c103036481c0c5402e11440b80401d40c01b00454001407502e010b8036401600c40000d50f2041c0c40000312 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 915375269 1250 915374019 915374029
    0x181518070503010605061804200301060f1b03050307020a0c080109020f0a1a031302030706032c030904020c0a120c1703040c050f041b0915020303010f1505070b01060806040b 76
    0x805c8441c05028285844031030642e00da118100c0840b929030158403a400e4003c0d0a91003203030100f0303540701241010b64075403400c034000d400d9603100041d40080c4414424080c004a0003081d41405264150901c10307981c0d40d4040c0101d0810508170300007401d1003181003011601c001c05500c0140703c50300c2510b45580c40c840901c01c10512052910848210004140c4040809181c0d40d01660704540d0a141e18415039005500207030501295402080019030b50f65000541040502006040142003841c5c481c1103404244441d070b264400c40c18903178025900050814101142001040442034000080030800c00654500070000385000c40c050b9110f04600c4216403081121600310b0340120b030700501194407603281a05110608400e4506c2d01d03809650340b40f0080001e0388000020382182c40e01d5492180c018200300e000c0f01200b1265060000719030081c001841655038213903a010503140c0c0d03442c80003880f11f961407085903180b01d1184010304055207130000060319600584802c5c001e020485003400a1248281441 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 915376519 1250 915375269 915375281
    0x11404020a03112110050a0c17100e0103060b0111070b070b070c020306040b04232812020303090d0f0e0d05010b03120315041418151807050301 63
    0x603500880c010790800001ea4041c80000b1604405130108a02c09407400d0f01c40042d482d00100300400750421040d08814140034420700381d0107134002400300980c0d28419402404440c40711400080101c007403000c40c02a458a0904100801c0030b100c0030344413581c6914111000d441c80ca4049404241c1c0c0b0381c040e03411210045910419a502c030b840c502c2c2840c015454403201010b0251000f801e0201201c1c501d40561014801c962041d800740341007a805013018a8854900161000748034880d00000d908032418040c0030400d01c2001d141442c50191a04204e41662094096004024507025550000501c0c02380c001c80038622030301c0c02800362528940944026070301300103440c07407440008002e0701d0309140b20714240c00042c140390301136800002c102d0301403000f0030714001d52100708040c0003801004200da5820b0700c0a64035407009054505005001c14000044002c0c00d0140940b41d02400c2c00540444002081000c0d0b030074007c01e11584245800e24046095036a09584a101141e000d200c80209190030140201 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 915377769 1250 915376519 915376523
    0x6032d0c0612041104020f160201090e060d2301090c06260601030e2505041506082202040c0509031c080a0b031f02090901080106150309030e130608011404 68
    0x15030b0550350740e070341d04068400c000c3d2200d5010b03500784809140e04038041c024100162500c40b040301142c10f03a00002d081c4000b0f03035110140184498080000c2621200c1d651011a40e02c06d41002141c180507140042d4900391210250a0303601c1c0109403014018614800000c940254940d41c0d281d0b100c0a40d1407803800c540403101a40680c0280208200394071950120041c26010b1040e102c01c0d0814011a2110001203121000109071000d02840149414444c071107220400c05a549907291a04401801c541c0004000f0304c4180c21100c3c034400f01141410b0b40c21101d0303600070720070841d030068080c003e0141d0300b002c202c2c1802032003181d01209801d00001d064001d003500d02c1d129180d09540b000500c80207454900d8845405001d0301014040f481264544841c5007800d0010140c0c540043e502880300714481680301c000981c3c1801020001b001140f08841e1200000c0d18000c114a641c608041c0c511005260030a03420480f82c196507085241c8a600000039507105500a02017004040e007403406800040d240 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 915379019 1250 915377769 915377797
    0x3150b0a03030f0e0a080304141c0b180f010501090509010902150f0d1b0f18060c08091002060412020f0c130e06070f03050c2106032d0c06 61
    0x1061020a000b0200440740c501c0c0c030314040f04d415280c2004100030140650001034968000b040c00c0c0503480b03101c01003040c1402c0a8440294481ca1004094090000d1080150103500c001d000700e4408400b03854412885004580cc4075006d491080c2c801d40201b40c00d100311400d0915141c00b1500d9208107006645100d6001415410004c01d0380c6101d5220f644a0954aa000b0b42d04101400094030341e401307410000c0d0300e000c2952140b00001603002d0503616401c1009010001c038020080703606c5039541002c0064914a14000c3e625450340e1800e82820310a60b01d40030f50003841c09524511344d545c00107070b0070721a52085001000e005034541d801e0381e40b54469116038406d50031607a00e40e05039013001c01c40080c5c400110700000c90881070300c104440c01c195003603030a034001441030b8020203800c170b070940611500181c01b405500d140c85000007080b685c0ca080d040891802803440000f04070f4a6030100814142c0281070181c203428074503c80420064041c0d5485566014098841d0720300c11032400300d054440450848807 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 915380269 1250 915379019 915379039
    0x4021008040b060906130c2f101505040f1d031e09030c0a0b0a090f0f0b0703030e060106230408060c25140615100e270103150b 56
    0x30404c100c4140040440b034018007044501d00c43d1b0300300f0340911015141e46842d9001809140c07000e02220408644c02c69468200c41404080c0341c0c5400a000001230803100c0700010655103c0440c505141a19800960b0140c20451440310810041d44401049840702c0d5550981070103100a0759100c0c0590405c2201e203500300c00c010300c49245050014804201d0007411740300d035408035800040244849410044d45040b0205020140a0300204c104000c0c0118880ba2107000b4030380807a5908503402d40c051103804003c0800e03807404050007030300600b0340712881c00d054508641c0c40d203500a005050002d900c5400901c811408400c02170600100c2d000e40d0440f03400340ca5141e8900041643c240d01c00c809800a08a03001c0100c424041c40710500c042c03a80c461031109181911540a00703182120140585400088411103902141d5400076040300c3d4403250b0401c41445000c41c40021801d0b1002c40074114410800d104500b1340d85e2010044034180ca10900d5145804c0e0442011002281d40c14a02e2030740000e0592 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 915381519 1250 915380269 915380281
    0x91606120915050f0403200606061c110c010b09010b0f07140a060218010201150512030c12070501150303090902030c0714060f0606090901090b031903050304021008040b 74
    0x242042240300d0096002d42c0244045030010760032110225004508242d040741444101980881c0b030421503101150181c079800c00071481241c413080c1c06840c0d10b02c20301c0000381035154155000c0c864142c440d50040100072080c04546810460b60025602e4901546080c1c012640c034074152043c203058a0007075150740d003021480003110000d075001020590303154490300c0004401900c10450103d01c24800d41005d621107101c00c0f003804d075480105071240d0540e41000c45581e4030000700c486800446000b00d80402c41904103000090841c4609181750410b40240c64400c0d00e100302107002824040c0c41a00204403082450840051103000c9000c0103001540d036020400c8401c4040d0040c0d43c12560308030030185032899561301c2450054292428401c69041b8200708018205100111075000e0020b03901507242001400c0003030070740001402000e00c00c0369194101e000940b0200281080e1321520070035842c0c400c07287c4c10090202c0d041110300704d1241e01c42000c03c03440c040c8904203d500407039010540700201c0c1c403030f0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 915382769 1250 915381519 915381521
    0x302d0c0303060f010e031f060e0403050306010e0103020405120f0708031204120e041e1416081806010f150201200315061603110d0c0f0813060809160612 67
    0x1043c0c00a04000c1c0c4028a10311580d010310450400d40380c0c2e00c1c0912490340040b800c01c1c05403811540589010500002000003203a0010200d942c4040e007480d100095000600c0160000c0c0035503001550442c2c0c24001d84040c61000048034010448400102d4605683e00c40844d41e981c840e043c0c4a049100c519004640001e101c0c0340b603110500c200d802c0c02c5082002e100b0200c0e0444511030381103402c140030380c818480c298440f44590880401c000d603811006243c050003c5600003180f03951343c8100140074000070803400303040e80100d01c00b6850409441d42035940d0302c8542c0684461b4001c19200fa4120202d0003c5980144030324002c0e000c49400000c20790a50704c0300c424403030f00024599403241450342080e480b2940d404dc01400343c0c01812080c0111504242070080410645040c25013459010004078004075800c00051054190301c80c9524008072858586080c25000d602c141003000000010301240090300541414441c092020480e00d080342d8140802c22101028821a07012440245100f0540b040e6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 915384019 1250 915382769 915382789
    0x605090d1e05071b1401021b0d0f060f051f060807080c090405070216060203090901050d0f1401020a17040213180206070b040c0b0c302d0c030306 64
    0x5a400c2c41d41c1056440e07140c01011220f8101300f2114005104824410380e241e002c0000c014020a01c01081103060580e400c800214003000c6140c461106c01130004204040301f042c146010342e00c50010f10042c5c1d6002d03107080c040c0906036041e80d800403080c6a15910440350180703510455120303948041c5240c80e101710541e05e1a40180c6050302240e4100701604c0680c80344d0003003d014810f154000c0101000e9200e4040a64060ba000001190801c00c16101940da44400c072a044d903c0440d011205901503103881540d04402d6500209000b0300b00107585503d0303a041d8040d010b104041d45035441c41d4208640d180005007003c03100258071044007040355008035a164000f04181010542c002007010807500003854541054070100c1d0f400040008002c01c20500b6085c0100810107c10040c0c01d043c00d070007805407103c4103984003c01c220501c0107a48000b54000d1840040c1c54031426203070b5941c40303940e503562069020305804046910811075010071342c0300080003100c014201c070318051800d5450b04000c01c00200c907 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 915385269 1250 915384019 915384077
    0x15030c0a0e12061003030201060603331a121321180b0c01180c030f32070e07020d0e03070906081b01050f03060108060a031e0605090d 59
    0x20100b40c01e94802102005994001d000ea200600585031851500a0941d07800b6001901010308256091413000d04511109002a03a20517158001c5a4624a5202c48400b00e90148202e80c01d14540c01030b980c0c42150061032400018840001c071f5694824003003050005089004140394880e0340d9144031700c00c420400c61464445454003440407007403080c4030400c1080d0307500301e00e03141e802c0003554448246007441b074403607512000803036495484180d44400e102490300744400360020100744055410054000e51100702e07060303403003180001c81e0030381d03000c20610802001d51140103206010f8040350710b40444003e14407078500e96001700f400c0307101c100c2c080f00c0401c0182030301601440b40b6030002c1403018507030287c10040c0c45500c00070f080039044038406142070a00400e20700d0601400704100312180c0351074411664010800c1c00c01c45269103d00780810940c40c603030380c40070f06001009401c0e0811480c3d50190800480e010700c01c10301c5140c0760344072015111145841448041241060031001c0c1020b44012001400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 915386519 1250 915385269 915385279
    0xf12070f06180324063c032a090504060f29190503153103030c0e031c030b06091806030a0b0403020d09090c02300706060515030c0a0e 59
    0x341c1d03a1207011b8817031010500040345401441d00401ca0300e408008510318800b00e9810b6103000c1441c503251407654114221000a003400e0f44944003901d0136241a4150080c4030041c0f00304080e2905040c400024504804148980307401c1030440c80001e191240d40c50f141001c103030108885d042d060001c2010300440c10f081540c00c1c8100540c001407582e41448018192200b0300d00600c0f40389060899035202076480c2c0860903100d03a0721603074100111244040c282c0420b90508000032161800c0000f41c80849040b01d00c103900d071055510091804000031401d40000d8040e071800e1183ca01c0d070004000190050303280c9607030002d1180184400d410b00f040300240d0000e00c0a01981e40190498030798400300380044405502680c001558207039580c5d88000128010640608204100100110000d480e081e03490142c00050610009010140a18180c0e10b00e6030b012880680303a4812044c940a0068002449064072501c004141c03181c5180c040c0040300c1c0705040c0d2900f81032600101130015140700c41404101e039045 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 915387769 1250 915386519 915386531
    0x60c07090603060203090f0d08060103050612061e011406071b030b13120e0d02040b13090b010512030702151305090a09120e030c0f12070f06180324 65
    0x158050344110700146015090140e500d1604601d241e14042c070000c29030744c41d0340c00700f001d8000d4140d00484240c0c11042c2460045000c1c1c0b01c410010701210f018203822440f07406403500f07200d1489684d50500c52007840848021a403a80e03602c50075030042880c8140c00c2d8004ca810403803000000c204030b0388000e00070500704407400490f840340c403031541041d4112003444c0800d8a072043c603020320000780404030745462a8940441c20b458583d02251140c50807400090283d41c884000caa80c9580703010185e1008842039030300304807180c2c81d800d1401040700f007031103940d0182c002281745e40d41c0f4410100032103502a030050005d006103070862030507115950100b000101d94814482005c43d59903142040380b4051815440701203140f403680c1c108030403100f0300c19440c0c82c1031200c0340300c01070b4a5860110f03c0080b941d00481d0103041001048000c14440e103800d045008070760050280129101506d000d05d82c00303030b03103181e0340320089038090201c101482d018500000c0c04010340d61a203d4059803a41d04520051080c0038404100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 915389019 1250 915387769 915387779
    0x60d060c0c02121f0f11130e220b060103110a050a030e0a020307060809030f04030c090b12060106050d022218021804050406020c0a030302031801020310050103091406090a120e0f060c07 81
    0x5940c210b4020709080000340581000100900325140d9080340c100b6a0f81d10909d00011007841c1d000000c960700501100302d100000d00c2e180e0290b80034003070b81d04400c00c000740d5074045500c0040482c0c1c40284960082850100221850540001c9c602030180d801b80042c980941020b10540d0b19441c010308024540c80304101400c050352094015100640c800c10001039400e040040d8103065854010300030307009184041c40e201b4881030000d0a58115885400c00e550380b08004401a000382c46200f400803611a9070044442c0c441d00302d0f03144401211005100180400074422010050f4812103030461281c244000402c14a480c0961050b5003040c82102c0062511288031180c034100400810143c001c07036408001c100d40620003442c42410402c1d144003c62070741c50564655641c1078801e001c0e95040666860091302042100c030301107002a0580b100b1601c0e68506829030941c3d41c0001841207586445505c0050074041c041c6900440302c1c00002d2900c90346032500380511050750401116030206200c0c000002603 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 915390269 1250 915389019 915389051
    0x70206220e0115021b04051005120609010c080c03040b150423010602030a140a030213080f010b0913111311040f060c0812060d060c0c02121f0f 63
    0x10040c200e00081085039071402090b50310f50f0802080321815904028240d01030405180600c0100300421940060107445440060103031a80d03540000d03411030309611601784608030012f246803045949600034402c607201c42404444003142030740c0d0b138480c0703160620225000424a40c4041d0303101703840e07607000c00c181e03a100d83c0013809459924a03080c11900320005509038001c600741d18140034040c0c50008528059540100030005100140c3d284070350704012496070340841c8290110780e4220b00d81184045815218020306468401c4a40c3e08410341d0301c1d21512450300d0409000907407007038202421a1848001544655486980c040140c4c0d511403c0780b14100070840251203180280301544c5052a00d8a05060890020310140d401490500080e0341c40303100095101000c07a0f05420b05808100980d458070404244289038043c4024245030514040814203030780004000e00c140d000b00c90031044801c4501c00203450300c00c0102c9aa400080303c1030440e1601c01c25130400c032222045d001000426041d4030014003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 915391519 1250 915390269 915390337
    0xc05030a0b0112050a0903080c031311040b04020c0706020706140a0e03010e0105091b0409080f0705070e2d06210c09010602160e0c0711030c0a06082a070206 69
    0x2617040c50742c03200d64070213140d44444c0030b0703601402401c011441d5052403840d03000c40501904000b407000fa090140f10140740c0302e6800904110380c010300300750b41b03443ca100c0d000703074555065006060062082c580001207840c03085800041d1201d505907894070304144200200c0c2c040b080b080303405030990b4a441801106520134883c061103010306802621010f0071031480481d058810b0000c0503c980d0032725280300003154004040f111480c8a42000d541d89400301d261960404000da4003c5182e0b10504080100c8444000d20002d0194503100c0604212200c800744200950000c0c2d9100d5000303c02c28860f0300c0d60130700800c8030b1042a0728140464405010410000f141e1007002d800810060b001100c0c01c08283c0b20741c075a000082c1c40441892011440e2400b03611445018108000d4851402920103e100e520213010008402001034005105207848401c0940150310940304604074000c4804410000f0941c00d28620180910764055441c00200741c080148a030050042c1c1c02c191700400e0300d04910000b60070700b00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 915392769 1250 915391519 915391531
    0x30c0e0a0b18120721150518030c120d0209090c095e0623030a20060403050604020108061f0c110a060507060b040c05030a0b011205 58
    0x416035440040b181403902c0101110014020307071100c0c0b591148104081100426290004035100426400d054488a400c2000c24044c2007554842d81a102084203500305074400c803081403403a0324090307020030a1503a91142e4526114550010042c040c50704c61600000c1c1072070071080c640035003071400007400690901d100b80c561000b200e0700095951064100007107800c10400c50031007002520280e0484241c1e84035881414254100d40e206d0f1030701c1540c1c0b624204203919040d40c400042d911070500c005003009000030301030b00034000f918180c11183c401070412030a844540280c0070740b015010540e00c504030503003c45d1200045001601300d154407174803901e0240004500810080801e0f09113070001510b00c11000d4211070054030210b80d15540020b040600440c00c0700700d46000b400c0c100642c00c2c4640d10300c0d500500503a0241a5100008049a11001a1500354095801040040118020001243c442c02c403000023040e018800a41024a5a40840007204040c141010300e54407021480080b00d800701d0b08 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 915394019 1250 915392769 915392789
    0x1060b04050303220518040b10030b010e04030c0609121106090705040203100801050f0718060e270c07031202120c0c030c030310090510230102070b07050105010602060f01050f01030c0e0a 82
    0x1f003106120520007102e4100e204680f03414201401c50712030141c00501400380340b250303d00e0640880c003014400e1550300400d603042081041000c00e40c1c544100c048022100540c0040c03524407886210440114605008540b444003c0041e20315140a00010b0342004207401440300c030510700051401000c2c01018494011520b500d08a803a04041c040d14800014011000309080594280b01058010040400600c011201c1c44025020400040180309103405c9404000344100c0a1040c459501405441c01c14420745550820100f290100012030240c40210400c5018500100b0001e20f0b1280003400034803851400d03240fa2440d5051140c0c03440d441920100c220907000f81c01000036080d2403192070f81207a81051212811850700090400c0b4448403803c20090070007500c0f007407546d0b0b0300810046005120300c80c405500c8400d94209180248400d205000146c0180e4001510b484420120681a504010082140d6050003001107005050312100c20f000d014404000e4a5030f580d800c02154014030380320007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 915395269 1250 915394019 915394021
    0x16081b09190501230307270620011404080c03040b0f0301050a0501030e060105011209140109020a0e04051c03020904020c010603050c0d0b1305030405100e0301060b04050303220518 79
    0x1082c40c0e0a01311075003401c16068206008002210049070341007952494100f201c0e824400624024990300c158181a00440450004209401034815104260b0560701c8540170106c0700704040c04d03142c1c103460301481c81036180c0008001421500140031018845411242096161030f40184942d00c41c1c10503240011010004001500d000380c10a0f020300001c1c030b0240321400d0341c407044907903482c410300481d41032020700d03054081190a03961080c2d2416400a0b1059030302c0640d179086034000c0a04000503030280140f954081070307242d1000c0105003d07a41c400010b041c000c0c9421130f02c85030038600d402e56008160b020000d00b00b15680318000b42c610a042c00000090541ca07614003189043c20714030545020fa69404001d40c00300340d603818031642c82200100c1329111701d1103501d0100d00b14415600190350004600400503d4582d00c025031488912055000b0061035480d48195000b9010318810154180e104110f00000301001d10044001e10f41100c116034601d64550000545000c68003080c8035203240340c84 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 915396519 1250 915395269 915395279
    0x3030a0804291501020c030106030f020405090606010f0e04090c140306010618090f06031b031403090f040e0c0324060604060c03050c03160f0b16081b0919 68
    0x240b500c0c0b600d5504039074682002003030b0b440381050404010955035964005414120840e4000c2c044424018001002001210f0301c2e0310b0001c0c462030009109a005501e0300002500001c0001485801242d050315040c4400ca5210811240d00013110b82c4550015110103065000441005015016103241c2c03123903245044440c401c1c5803412030164805030401c250000c1c41152121100303241700582f00841c402280c80c2c000d00c060b41f0302601a60340b004003003c580d8a0b0004a0001c00311060094900c0307101c90320401160f005150396071740103543c10300c0e5000d41405010391061503e6440900240c00309030695684009200019007411208090710004840d209000451249200c40361944950209c0301982424100f210081c21940c1d0080d00805000d00080c10111011040040d41c101e964450503028185100d807034503484500361610100e03007a514503c0800d81601c80d03c03640c10b801c2103035591100d21540c2c0718503035541c07855481c000d0490070f441d040003e0f049079118072804200800c92240a2144540f42c8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 915397769 1250 915396519 915396533
    0xe0c0906070803093030100e0915040f050f0d02150103051c0216060e09010b18040f02040810021201080d120b06040803120901110c0709050c0903030a0804 68
    0x40a07212010010320324000c40708881001d042020324035503074a041e449401c1c2c6c4109030f0005091040c3e000004144006003015207840860303280c442c882071901a046d4580e13a42c8002c0411700c040d03030031080540105660b4040000c850188560080c01003008042d00c0f0030b96142c5c64103020a400c4552800e8121550b141c0080382c04000d04245071801c1c4044074099851529a00d8642180070045200a41d04030302d1415810310811066841d00c250f20051902255101e80140c0811a2503d82c03d02442811000142c6d260300441035642e0340445402000d40b422802c01040028040e0310070100200e0350034070010a8808080100100071800c0340070042e500c0c19410110005010305034000f008a500030040f1400c1941d0005503090304040003000480c000d030500002410500a0b504401c03c0e03448049070b0101c0c0b41b400064014091100007008000300051030003408024882c2c66501c0d0b805500c240380410015030f59074007161340080f104210380c2c20500a2000242503070b00640c3d00c40005058030051105020034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 915399019 1250 915397769 915397783
    0x9060306080c0d02040c0e030d020a0606171e0304080d03021b0601030201121505060a0215010603020c0d05131a13060e0a090c020f1e1006030302070e0c090607080309 73
    0x762100920381403000d880000c00d080d488010003170003141c40782c6060398180c0c09845480d182c0c01004050301c01a100a0340c00a55a0301c00441c1078130007030300303100000035081d85001481d0300960501016004840c0c6200000b034103480002a028000d202c01c000019000c002802400403000481d82c5c007594400103c995602c440018504400f0550088001080140e8100c00c101d0000201c00d540444d5465114143e0000c1d064940d0045800c03070000210315038000d42c0401ca4045024801c00318107500d17602c820041f0103d009251801e001035001309041d001c0140148058503828006541b40c9200980391891307410251901d9510209484000c1f6040304200200303e440009040300e0300c1c10314400c900e4000028980f014074880e1001660707507200130084052003802445102d0030407001300e030b50013100000001c4114500030340304d40103406085800c01c0e405a05000340000c89030558000d046042c00c1c40c0c2808504203015065030342850040011091644a100140030001d00503400f150301d0b458066205820030003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 915400269 1250 915399019 915399029
    0x703140a0906090b030c04030209040c050409062408030d02070602040b0d09021311030c090f100f0e0f130b27010302090f13061a0306040c080c01020607120b06160309060306 76
    0x40140b01b04004203c02d071064400700c80c0c0448600130191190f0408a8443c4032540013907801c2420702000b2014040306402400c1d00e51803c804010b0b0b113000201004901003454052a0070702e0b001080840741d50483da40103410414041c860040c68565507a215410940c000b05205150607210802502949800429114010785051051010b4074180c601540c01d071000900e811402103010403544141e80360b504041c5440d5001070f04281d121806140003a1a80d00c41c03a10810001d84078090215490403d480044280a406003030708071502e10f100c44150140241e8410356404c480600e101c0d603030b20b40c03d181441d03801d40440700c86200154114014444407020040c4280c2404038440305100c001c980b050101080c0c5600113000203282c2d440e10341003031400d40d40018002d13418401c2c90f061100303101800c10144100c1d45520101e4040c56882401a82c9983c1f04550341e901290711510340c014402500e4000710003440006250602d0400c2c0c040400407510915882a000610454418425950144a02da014107 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 915401519 1250 915400269 915400289
    0x6060a060f080106032d1512210314070810050109120213060b0c010204050307090b0109270203011d0c0937121707020a03080703140a090609 62
    0x102281d20240c0450818842d86080503a2666130a101076900000d183c4014030130307002401c1b080e454810000c0980400010306440c5100c5040000f55489844010300100d17601500300d148a000c10b0042140850f07a441c120024552038002d20503500d159501ba1798854030068540740400e041803415044800c1c0e041d00010b0501040b044107100c82d0411051040000e03604440008115a594012502401c1b00d039005420320303000400c14507a14001074000c0d1064070b0007070781219003141e03461301e104098545c0300c420300d030120b01100b1082c0002a464145080d0305244403254420800d26143c030030040745d0099110325451134642144010b401a50344c10070303411180d17580109040420300307400182511306208048107641610704091542d00d03064034541030100c6002d01c030010510b5032400003614640000310100d030241d075041111694110184290b07030783d8a401030903210b0303070300c1c00e42c0c0c0c2d10011540f2608003a8203000c44840c060307a05450324002800b02c210700d5903ca000081c6842005040c0341c14503041b045c112 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 915402769 1250 915401519 915401537
    0x5030d050c01060e010f0b0304050c0301181103010603020105030c0c120a0804050609120301170c190e10030c0e090c09010f050120030306010827010207030e1917190506060a06 77
    0x540c404004c0c2400b1f889650350415070700c2c4c643c0d10309540740110180c86a80c00d54200000050f80044650342c182c119406001000b0b04074480384109400c035143c6010003408100144046400c07404100050301d0140d554904407100e19092104040054100300d1450300000c001c4420041004400d103c0b054002100030020214031640d00f11082542c041409003261010021640c050741d000104402140e10074094400550240700140341c00a08080380600d136006403503200030500349508506c1c01000c4035081241c900f4403a09200005511240162400c20148940c03801600030356038100c4914000d103d8960a080e00314a010000351040f40d4021071102410791100200692510200840b03601507404d1801c00810303595a0341a0099001c0b000f146184030310320048000d8214015801031104600a807a40c03000c44020504101e4814220325642165a0303040c9000c01020405203400c4204080d00700c00d444280c070754a4802001c3e21015441600d41c2d520110a00c4180e0604c4c001c19000303040245001100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 915404019 1250 915402769 915402779
    0x21f1e020354150901020c01150803040e1023011d090f04020a030c0303030204050910050607033911180f062d13151701020405030d050c01060e01 64
    0xc406011011080d03030b507030420400d12292900f404030b88810380180c84a0145801d110041300c0c000d4201c840581d505602c1e01d5111071000c0391030711240d400c80d0000e40c019403420b41020600d600d55040500003010100c404000824012644903030b014081c042c0161400703003101c0c1c00340014002e800012400305c041c550746840c041c46403150b00070603a000c041809590300b69181c51010544402e02680013130306503513054502008050382b41e0014030449074201c4143c040e503210746040c2801d640161188550100741000366000280c0104c41f003203d00312154030490075801c1c1c070909042081092006a0f010740101252010411004903002c6607481c00554100c503025000130072004443d07601411401c108640b100c0041c0455507a10104401c6078000380c0400a2010480c080707095802424000750b20492a203c0c04189201c658032480221290681002101074030b043c0c00580d021080d00c4950880755005c110205241d1410854040791346a541d0314560f883d61814252070860319140c11001e660760b09a001000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 915405269 1250 915404019 915404131
    0x1b2f120304030c0228050d141203150a0608040b1314150a02040503070302130e030d05070806010f022806091101120203040309180f0525021f1e0203 65
    0x1042d06d2042c0c480f199201c00c80e00f0803a0580d01110740524051040c002004040070b2103501444c046e04500212050b440314417010003103950101e0003020700140d4100001b4000c1943d102c10903400c842c00c0c4075a42a0380d50280c60b83c6004124030340e0007404030750110320207285400c020182c183c0d1001d102301d000c42c105802d140000c1e49440d0035120280c4103401d1a9111541c004040c0d104241d180000d01c2200c0d903c007000d02c8604082c12003207400d14007081c603030f0300081c1c0e10354040c10f040000c00c0c0c4d0a50181c0081d00c02011401004843d49242400380c103800030303840740040d40070701c0707002421801002c92217184140500014015184000d4100e41c40340103201303000009410100030707015600a11600120014081c136010000c00d2200c5060a22905100520aaa100c29014600140b00078000d0030104420200700303a0740c4a42d401c6665020f01c14a01e4149a002c030268440721402c1c80890b0240b0a0480c2d01401c5410798200f9100c24060b51100c0b4424a00038001030302c4d00c01070031100f200c0615035090b203501d020 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 915406519 1250 915405269 915405349
    0xa0f0201090f06090305120406050610081005100e130e061b0403200301020d06050f010906091403033f0108060402090919061b2f120304030c02 63
    0x1880d10313403651803800130940248103903845001ca800309043c1c5072900381881006004203941d894001d001912200c00030341d2240055a202c0d044070300c45007030058548000e02500d40300f4030806d60300300214a581d45a50340d031102c3d4858800b071f05c1100d002c1201c0c42c0c2210f206040c100c0c0030b070003e0f69040311072541703c0c40071101105403800c4a0304101a0740b81c00783d440c0c0d88000c42e40e014041082c0d15500c0086c064071520140c0e0b210302c041d40e4065407103c0a10401100541e09400b05019160101d442c0e40b0b01003204d41184410020a404041c0650741090003c80c00c400b0f001c280c00c408581d480480f00130200580a40c020602c40c0c0300c6140300741c11023a514040000da00c40780c0c0500041c2c040d00d10403002541d10700f0204000034550b0425811805030000ca0f080c900020035080943c0903030786c1036100b10a038200b4070551040c280101206000e03501c1f000c2c1820060700c20104905420307254019600d40c450208845000b0718440d600031703210a0031801c1c13184104110303000454108134020f510714200c0e0140d00d801402075 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 915407769 1250 915406519 915406523
    0x11090c04030510180c0803030a0c030225020d020a0e07080c07030f03050a06081002120105040e0d0f03090204090c06030f0510180207050303100503060c09031b01030b0907050a0f0201090f 82
    0x10326550b0a80c2141c0ea1301c100c1000180c900d2500c04400a080d850020045105d20001e210400101003031801c200d085e0711035a0140300c0f270b00300c1d6440407400100c48004d1203422140300503d540030b001e16a40c0400c0340035007560b1164031011549410013500030b0b0400c01c15648a1200082149403050702d50300901b8030346602403070508150303075440004c0c104005507112101500020702199081013522041d003000e5440601c15405003a182000050340d82014003070f080034289254040c114010011600f01d038148440e032000010541c03036030486070250f1a184640f00c01c4034007c039010741420307041000103800e890100b0700221005d071801003041031290440c2c4589080d00c1409a400105080d5904904060b00401c10701074801c3c0400014800440e600c2801d0508440d4142c05640040e5603494103070201e07024824555030181c115501300c80600e0030710026083d1024050400141c0c620b0300c0700101e0b1402c001117407100c0100704005001e0080503040600c000d40825071313100038082c0c0075142d554040181070007180 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 915409019 1250 915407769 915407771
    0x312021501091d1b0a0603060503060402040b0a0315091101080609070516140705040e0a030e010513090906050919050309100908030310060906081e190911090c04030510 74
    0xc803654a503401e000080651a228225484005030000d056206a04101030358840d40c1d5017200003a070b0a0083c0909411148020040d00c055a10703034082c08080e1a800c0d04040c1c1c002507184011002039004010b8050381f0501c1c040c000b65000e201d1511802c8641e01410b05030500640c0c4082100315030b105101d25078040c0e25441d0950300d95100d84581208040b02220042c0f550b45802c95910f44100c0011701d940484070202d5062002c0328400380859100c90700c000016001900b0412200c40950043c0003c05181c00302a6074004000e40d100f030580100e42941808a4400da15032042c007000407802c00c5406a51107000151600c2e202c80359403299a04e11698a1a40c0544030010030074000c64082c4170039800414040c4107581d500d10700b4803805503035400d03d8010030000c40c000c0d41c40460a00e00c203103170300c42c0301d040a400c1c100071401c1e281c066400c5444009003401c10300c9143e8140103003000300900441d401c3c144550384804c0b040080030100901ea0303000070008000224188820000308500040d0300030701070f4203000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 915410269 1250 915409019 915409031
    0x14010507032912031b070603020c030f090a090207030c1b050d0308060409050f060123010509010c0204060504020f04090b041b2012030f0a0504030f0e030313080304031202150109 78
    0xb011811082c041c0000c1c040a02020030088034180305041c1180e0802800c00035260b01c41c0e12503800341c040f806040c101c890720f03074414007080780d2014001d0010068800c005104031034069071440813109a0b0b2145d00201d000400300c44135070080085c880032071900c90380380e038111114281c14000418841004104042e0402c2040e00202d9513a803119400420007a80041c00e4030300070054203040c01d5446100384188001c20280b0700d0012545122481c3c4e00f402550160768043c030740300c0000700440d6070600c0f55034145e91280e6221070000381a613840c802007020301c03545410b080d2124540003410045680f1010350074021403c000780501030f202c0c2c40c1c2c2441c968401c9810411310034034500303a0481e0704080b1484e43e080d1f2403082c0d420034059440340102035072051003640500646680e4101e1043d0a885d01510020086a821854200414000e500011110501804881c10b1031841d007088020043c8030f0340101d1030758000060a105000421050a00109203400142000341440601c40c05002051080b41d81c0306586407 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 915411519 1250 915410269 915410351
    0x100c06060509010803090114070f020609040f0f0c0e0102060105030c0409290a1a0306040b09031606140601051c0207020d02031e0601150203031605161401050703 71
    0xe4025005800302800149a541c0c580d1052a503d6008480041c04110f4a1600310700c0c2100b00c074121070816901000843c1240e445601f40304441d04038160199004d9210b4000055000941c46400340d00b140300e110100300c40043c0d04005c0c080e10301103d0305a04540019005108540340010030701011030017980c0001c1c10b80d40606001d400b0b14410314058070020264031180394100000c06105006081c0c0c4001000260030709040469000e214590b0b05130543c01c101c0000d00481c5055501d00e03408951780080c1c03440c00070a4080d00d4480420aa011070701f541c2e80b2508405c0d5000e040f031030598882c0007803c0c041e2405813002c15010001a8103e40b4284143e0009490300c21516484400f50905d503000e400c03a0b000002c0800c913000303c46559240c2011074898200002a0820f81041e118031642d0300d0380165203962180c511080c04107110030b1182c028032404110300e0740200448100e0640e0b030742c02000741806001100310303500c0c00c0d0340c0c02800d0402054240002250762054a25181c2021038028090b8031144c5559 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 915412769 1250 915411519 915411521
    0x40e0117031c0507141c0e03041a030f010e070504140109090606050309010b0f2209020d0302030a171501211a0a0b0c061609080109030f0e030705100c06 67
    0x40407101e5105100382c103201088641a400060041030304e916000c00034100740d50b40201d50f010307440c2d03a0110164080c100e0511101c4c1a40078210560120040e6480e0179102d011b180400f01b5040f00c4030a811000200f002650f000b8000400d000d460311030300024443c00c212100070700f203006a00420340d0a8042d681d2a00c04c9a024100c41c000601c080f540501a0f6039580030301400680044541021039401e2111800315403400c1854091804001004a4989112034a50884000200c080d1086944c1c0e12501d950259480a4010050070310942c003e6550314032000c0d0041441010302002c82008040c00b06110503600000040c40c0080420b1820710b1100e40078034190300c01c4550340341c041c4401c946460755860782c0141301c211a09080c034098484a03840365032520741402522400803035000580020001c110103075900c0708040f080e214641f4107060300b1034480d0b00d600e08440650718114003041c10040382c400300e99007100300204005c0044024041842c41c0c41d0200301e11001d40c070076400c104003090715400108112 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 915414019 1250 915412769 915412777
    0x60d0b09011b0e01030f150b1305130213060f0905130216060e160e04060504030c050102031905010b0307080a0e0f19021503010b0706020f070204140f0606040e011703 73
    0x4082d10008112062080640410500705910b4002070600000608240e00350141d11568011456002101c0d458040c0002050b00300388003d0b500080d50110010702651035000e080c41041400d030005a440c407124550451740720039948688140b1404081c00a0041c1d0002d00620458500359041320402d1400c000c0007001748500341441410015903842c100c180240381c1d01003409800e104007103c01030914503c0c20307184000a44621b50180f0508400180040d1080d00899080b074801d080503c44c03040e45664040c00c4e608100c60014407440288640300b2010807602490303005080205403a032441c00c1600c001003029000074490312601791110700008002008104030304004410ba0291160820442d46c0810070308503140e4268803c0280d0744400c140c0e14540d1017100d040b585250b1036140b074910340e607031080c000e900080380c0702805003c180310341c01c0941c5560085481c0550001ca40d15498a420303205034044031401b40c01c481c02400c0c20702c010b2101c4240c0900450540d5500010b21070070704c6075080c400303145120f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 915415269 1250 915414019 915414041
    0x90b310504061823010e07120303020f04030b040c0506030705030f1f1212021c0e030c060f030702060711030a0804111206100815070806240d0b030303060d0b0901 71
    0x2240c8000051010313070040070381079a800a01c00f010150401048500740c030f41c101142c500c2c0303400c80e0300c2c10480700c1070310710301d0412640c032a05000d81454085d400d00046900507a00991750304c2022400c202c01c00490280b40360151004950305402c40c1041c01c0001c00c14040104070410310307640180414603d51a8004130b00882c0a801c0d200021242c48000500000341c0c200000c07500700d02c00c004080030240c0089030a03056640d0080c0081c01450741600d0842e190a400242c89806000d00d50b018100c54803260001c00c170000703091000315078078184284002c3c80d1000c010b10f80c03410080c0901900c4107166022040364158001031400080b40d848500b025100c3c10403c50f22035a101c41100d0026948620101c0d2061040120f40b00c051106a510345040b0f0301d4500502a111151141000041029000d09880c0d6000800503203c4020a420703010b0080c6a1107441f82c0702800c411011540c02a0141795014204001c4400d6019605605110011138184401c107040108500802000540503075401d40c01310180d20 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 915416519 1250 915415269 915415301
    0x705030718081009020906090f04030c08250510200a03060801020309150907030f0308070c1502030907091e0203060105070f23010203040b0115030b0a090b31050406 72
    0x281448a410010304004d40b040307006164100000341c6500d0b1070180319100d0035255400d101d0550740c1d65421600a041d000d002c07507100380c040c0b010f0f0312018000071948420060220b2440c15508450a00340e240c0a03810042c4501c541c107105842000381c10144d0300ca5440c00c00b000250303407221685a0213801825036074203c800c0c03c0d8408030400c4a0004c2c000760701040c14841142000403601c80141958803a121400094000018100c4004c00a842542c041d9070040c502e20b0001c4480701582d81c2d06241c5600215500c5609801200f4401000c02c00c1c04840c0060100c01020410b07080114203085158a0042e118500c3d01c0c2e0100000d080c5901a0040b01d40b29a0b00c0955204410f01b1482c1c9241520454520012406048205d035000513005108980c0102c2c0c005104000a030b10309441c91040385020200102016201c0a04400503144c81d0440405000236003c08501140d910040c0719126111400e42c161801402045020102d4800800394541810100200c1d070759a80707003040c03005005002c9440d0f40d08 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 915417769 1250 915416519 915416533
    0xd0c09120f0209151e1302030429070206071b02190602010b061e0d143405070209061f080a0b010e0901030b1f03060506030f06220f0519110306070503071808 69
    0x48545011402502e1040d2b49624150f5030071994502080200d4001000da403104c5d0100d621a40142507690401201d00380764126541143d0200d0b8000c10801c0031103c8000b1050000d0143c00e8081c050240c06620a49601e0b082c174083c1054a115075148243c820684000090b6110944419401201c1411441180d182090500101004081610b4901810781105d0000c41462140c10400e01c01c1d11f84407255202c0f4107012a035020400e4010000e0001076024049007001d100c03003010f03410030003845019900c0e80701117450800418019a40c0c51035a007410030581340c0140065680300c0d80d51318107580e008440c40c10603030b0f50301c035128000300400038241300e08104d9840c0020030442030f508041d105020990984034048030340303551103680d420290b0b60300030212500740c0310a0400b8505400110441e001c0c002404000869403151403d154030703104100c82d505118142e000a0041c051440b600e803c030258010b03d41c0d403400280041244c04090801c0040059100a5244400c0701480750f070040c14080d002d1b1110 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 915419019 1250 915417769 915417773
    0xa0b0405010b0d0f0303050c0702010e062b151a0f03090106080102040f05031e0613020103020f040305210406080114040b030709020301090609110d0c09120f0209151e13020304 77
    0xc0b509007401100000c0c01c7c03600050700510014150303012140d06840f90f030981c010b00001c10078590091000c1c50803052400300704444940d202d4841c2200d0075120040000c0d0130714420001d030001c540030741140195070000380040816031144401c48407483c1100050a07201d4540f00d04c840c2c05401203038400e050540c0045008109c0c0c900040c2c0703135000c54004800301d074500c50504040f8102e0928122091400c0e42000001500c4048144104070030140705250061400c10131051420f11a0481d8000391860b0f40407481807100181106148480c0e1944054220b041034a01800100070f49014000e2604041c2c0d403840900140d203554000c004d82d010300400359480503840d5515100290424803038180b0080c00c00e400012034850a102d10f408620b141e100740d510301038100544002a1480c803040c8400c1100c504000548049091f1b0604100c80c45170400341c8000c00b4500421280c0c441c00717032140c002803200000140c13443d40c0e4090001d00f4041401400d07102c0c040c10000041d4600c1210040080b40c500020410003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 915420269 1250 915419019 915419033
    0x90106051f0f200d030f150605030606090409080403030f05030906060d020d0f0b160e0a0e06010c0f2906100807140a02060603070902030105030a06111c0b0102100e0a0b0405010b0d 79
    0x10400125075000c00060a0020300d420540d1041610b024804007040410300c0523504c00d03002507500c104040c29881c0342c103110502040c202c4604070025100c1d8400894203108155101c031103502c41c1c0040b40b030020b04500704200c0c031907200d1501400003880b8100c40c80d60790341151590030306060129000510726a00c0041c03420400e000c0d01c4101c8420b10b011140503010f0007160b00814000fa4481005844110000e041c1200b003440f65001408183c1031040030340718080002d9a4a240002c11841f03541c0c04500c000441e54031101c00009050b10400b228940800c0004589403400c1101a005092030224a03c0d16111815547d8683c80c03081d4800c000f2000a04040c03298001444c0c0d4010ba20076421141419038420320041240002c0c011907606804c050890000305200c3d41040303c034840c16900c81c03450601101c000c151600140c04421506a443d004c8400b02c56030140800003000003800c00601ca0010381d041c03202d4980c05030400c014400003100f00810b0604c60309602c0300180c034070081c00b55001071203103091083c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 915421519 1250 915420269 915420283
    0x2090702010b011710090b030f1c080a050c18120706020c03060112031407080c011407030e1f020703030e12070506070e010801090902010219060203090106051f0f20 72
    0x2d4081003010038000d007108600340d000e62054207035240041410781807503054005003000c5151203504d88a1144081c04001c4140100301c60040c0002c00903041d40c00c000c07400f5107488401810700807032134540020080005200c80c225401e02c0f080d5403103d0120a942c00c005000350140d034950a146120301e1902040041e000601070309485000c50455000e0313079950b120001d03900c0b0b842c0c1c0014005803e0000d2419400f03000360103004924850324806042046103200242115154040400b031003441e00d013403115003a0184a4020300826042c00740c00b44943c00c0f49400344042d0a0245590790560000b001c02c103051003a403101c0400000304c4241c0c0e24400000510402c1600b0290041c0d03981e0190101150000780120402d07111010180c41d088156032074050b0100050029030001ea040d0b010704000000c81c000108148031055214403001078590800b083d4440c2101c6003508030780d01480240310760722504041203040521803116442c00764080340c01c480c011a524400c0703162182107a00089100040a4000f0540b0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 915422769 1250 915421519 915421541
    0x105040b250c1802070f0f0c0e07020d0306090e1510120b011409070f1b050f1e030a020a0b060402040e04050a021f0804060f0b13021314060d0506010c0209070201 71
    0xf89511207420108100f03d02c10748500030803907500800c803180000c44180054040901039080c100d0030640d9a0583d4030440030846d07541d401070700304441d5a250b4030340521620026120b800302c20800b80c120301d05102c0c2e58240750741a500c1628000b00002c8c0f85641e16a4031040540007221013045812000e01c0d000205200c01c1c010126065400701c48584a800c040940606c0307030080395100614002000000c1d1075040d0188034180285164642c1c2e00045031041100ca030042040400030081050040c4d1800c1a42c0741480c0111404d070802c0103102c00895001032502c003510f0304651844401c2d107440c03002030300912031039022202e0400c0e58801c001c18003002007614065a030007030b01e9017481c820300c1d43c10445200c81c0301d040340d101140301c40d404140403c4080c0d000c103a050b0a80c01002448078081c10024030002c135840c5840d0f46450b00041c01c0c06c41034290700d43c00d1009040f0241103070a0164030000258a501420140b18629980c1d42e00141d003580c8100d1078980600e070060402161b500f0b10500003400303041c050701c0d8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 915424019 1250 915422769 915422789
    0x50411070210030b0f0d1b0b09060d020a0201180f0c23040e0f0718180f0f060f060b0c071a0301050613150302180306041509021203040603150b07020105040b250c 71
    0x1f002504004e400c0841e0811280244035500c0c002d8050f02040c02900f000300741504641d0f80e03034840010101805081c0f0388240c0a0f50841c0900b0010b894000c981c0c0e28560085a1140080c404440080e00c401c0310b0718050381070440e004200d808030121160720745041321504650502c140c0390002000c2841100d083e4400820031414004030b0b0384565000b144065a00c001480d403100b80606002040e20b00c0d508052484c4141c1001c180408580c020205441c203d8202c440c0032800026415032901041045030001d1410409200c00004074801000389400b0520034103000f000000f03202211a054010808040d09103214100501020200c00500940205410321050940350074040032910300012450b100b01c0c0c0c4013124110301111100c240016010350744c4200e82210601000d01a4903605001610103088166000219104c500c00c140d8186440c0c2e43c45100070304800c20003a000350741d203c1c00703c406a170b848410580d500c5100341028010043c2020208003c10781e1003d640d0100308921250b80201c4d036074504 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 915425269 1250 915424019 915424073
    0x412031224060c050d080c0d0c021b0d0f240c0e040e06090d23040e0403081602030f0f04050d110a080c01050921030f04050411070210030b0f0d 63
    0x1003a140e0b09030f280c9015000b58002200700c905240304803200d07913112044020542c04c00f00c010b03507080140d5003826100b2000d07030000300b11500f21809158115412400c00c5034044c81c0f01400d41c907680544141c0302e10141440f1042e20204803140000340c0e444042c01c07a82941040707000b4091000904010269129502c62401c1c00031120004100195460144070000050404491002d80640341c40c0c1c505901103210401d811000d50303401840001900080516030548400c9140904e8002e0028000502c2c091000c4030302e00300b00032040d9001040c1d651442101802564600001200b42a1030065a100c2a40b10590001d04020411900c1810080d14819161031504986410076552100c0e02004110700183c0e00b803010481a10f4150140003d101c044204180e005081701d82c12411944403030000c14904d00c1c0024104483d007011700c40c2c3c0d410f109948910343e00302011640010030418003401d0305410192126110a19076803802c007460500c1c00010004c101d000c5071460300c00c0600e02000241000012000c0d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 915426519 1250 915425269 915425279
    0x10315050c03160201111c050c0c03030c07050a0b0108030c0105010602071406090f30060115030c170117010e03040503030f030a060b1c0f0c050412031224 68
    0x1000d41802840320380d0030581541d4401e24010414224075424504640d00c0381504004940000010241d00301c07880c0b00da1101b60082503aa000791200075140c4c8480a900b0071003095000808001d50380c0124250f02c45a0f44d8020a0509510b00034030908040c125540040c0002910000000108501c00042c4000d02042e80e94000998642c800f6106800c001d04d4140c070181c070b0034901400102041c407030040211045440c4d400101d000c03070384400418100c006520804000618004401035a85104030000704003035810848604408ed10f481c1781d030824142c454109076492800752510b07159000704440511460f607550081100c4094007540e04074225480d083c541416503001000b142d090b07c030098001c40c80c2021442c03d42515620050039555060b540b050081881185680245000320004a04c0b41011811032040000ca580c14580448258641004082c4040d0068241c030304841c60424111181a401c0c14190780d400e41031400e002d0582d1900c84281c070100d1172490041070405040e84200c00490f00c0d4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 915427769 1250 915426519 915426521
    0x1805030c1e043303120e0103090507090e0f01090c0611190506060a0911030402191505070201030b0105070b0402040e031c050f1303022508100c0807090f0506090f0612010315 76
    0x103000180c2001002c078017481000c2d0191241d62801c410600d40001c02036940c5c0c45050800c82c0c20f8120002941d250901c1441d81c070010010704003c215614020000c080030b0741d450f110102d00c280b2460040c01142c503600b118820060051040140402d240b200045400c2d140c03082c1c8440c01121618442d6030f03a02b101040c0d0414911031031140f0381058000a280d030b15a6002c03c6006c0e0041d05141c41ca80c424160041440e1017810b00b0501076024075218107498074418030014013614441a002410807205010280203d40010b050540103030b01500c000842e0441c034540030781503103d541c0b9a2841c08404000e0803450015a82c4103500c0b580303454419840301c1c0c860070540941c04034080f001030b0041c2d01404a41010520060001c1200f902a0610f004030507980c041c414200410102910000d550b140031501c2c0207504125003641c401c80510342031015905005a50400c40c0040c09014059400460004125191405481c0c0d01040041c01c0c10385480c90040004022282404111140d9100e02c810344182465 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 915429019 1250 915427769 915427871
    0x1090801090b011208041d09060a05240301022205040606020601150e0d0b07020a060f05010506070611040b0c100b040506060910090306060906061805030c1e04 70
    0x100605200e401c2c2d10341140c1d603013031030141031041c0e80040080000080600000510030101d440452241019223081d05c4d44a0804074001c110160300760601007004000ca10b200c030341d04400003205203680200c0300b408010038020b025160210f0101101c803d610050107036008107100842e401203c0c2400b40703589030030302261204000e00c589080c0c400e280b642242c0342c0380904110380c0f94031000b9242c0d00d400c03101c58076802e030070f00d00580b51030b00980c0102c100741d428088240684508452024000e10131545440d0114105204540380505010f507107140503004001560200d400420148034043d0701e03500741a5000382c40d481c1c0001c4038148545860402d113154102030107810f225420050156007401c901c1c00c18402003000d078000e41000c100c40f884010000404920841c000362003500d90000e6071034207000000d40004040b4045030354140c1600c03810429564009150300c154002a02e18122014443d840e07849103104020540358030030308000c1c101d0160f50754100d44400c4070503542d10210718000941d25006a80705 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 915430269 1250 915429019 915429023
    0x12050c030d0203092403040f021f1e02030c0616170c09060325020d0f140429070609060f2c0f03031f051002062d10050109080109 57
    0x510415030540f5102462011a604100c005c0649034080c4640c00303a03c0e4012202120a00156050501941801075070000303043d003d525034101c00b01003000f002d010080c03c2d0800095003117040400c0210729100b030040e503402020070000c94800342000d030a010f101e0354081c00343d0030000301c500c2042e08005100d081e005000d00c950001c80c0e480c190281c01404003d5000900c0303160b05540105c00f070a41300a840c00400034101451340170b40900340c1030700001065401940103510030000300740e0750340340e0440c11281187c0c104c400f15151145c05800c0c05902c04500454602c040c20044008500401803003075a8000c0200580708000412004071410b03132038000c0710f00840c90858105641c040032016006400001030508140204564401e1040499a071035648201e41c0035041c0754003c00103444000712070741e0860281004a4808180c5045d500b0001d503030302d100600d100c2040c0d52040200034803600501071011002d440351190b410a00e09240c400d00c1c170350b80c030740300300380c0018030134040001c49100c10300c180c1d00f14036 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 915431519 1250 915430269 915430273
    0x3140d021b0120030307031b02030408060a020306040e07030c031505010b09090402221406030102160605041b030503090118140d06020d021611030114161812050c030d02 74
    0x4407064011140101a00d08040b149824150202015a01040511710501c01c81d5004942400312158071000020055000802d65109100030300c01e2260200381c079988084030035001600c03503690000040140c06145444040b40c003e200011060010304403405c001c0e0390040b07403840304017421035064000b11134091042c3c02d903002085c0412207541c0fa000c1c0005410030300042017072120103c0c2042e4084183d0445000c41d40d20742e5102d80e00303130b19983c000342100d41c040d5086000b182006c01c0061180a0030400c100004c1c5001d40e902c00143c1085210355001c2048200c0800b100c003401e0710307840e10590307940c002000d03c0e010581c4822034004440264280b03174140c030f401d150102d525040070014032034059a01c07501141c009400384964075112a0302c0c030250450f022124403040c0100100d013000d50030a042803000038040e9050042c101030300c100e80e01031542c0088402c2c501c11210030b41c545040b1030404462010b80b48640841074001039140c0808441c0c0d200c5401401921100501d42d003c066540a50340c11050150b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 915432769 1250 915431519 915431563
    0x110c0f0619091103010513020f04050f0414070918260a030b01031b0309030f0e030a080d1806060f0b4e0a061502150c1303140d02 57
    0x45039442d000200400d20a0b0b4402009120b084002401e44104482401040c60701c4000b00007545800c170001c40c4030100554040009080c000300c800b142c00700042010344458510300705422401000c00a20b0000c045080f030401641a481c880d5070022000f01c44141c50360880c02c508009521030240d64228403908003c0843d14064140b10706070090b2040400403030500d65641c02e001c402d8540b52940c102d020000c1c0d07a00094242c1540740c00360011101810120401040701d407078003200c1d00d0009684c44501d030400481c50f121048103020030043c001c2e610703100581d00d20011032031042000c20341180c0280c0b140320040140756612442c0c00c04072800f4102a010b010700c04201042c1e140c2e02110359020066140104a640e0644184180e19150406a4000080104032810400c90300600d1045a002d07100d0851259100c80004200941d50821500800116010400032980603107184041350b40c07044c1001c868045056880c148100302128076046000035000f05450700900c00e00c04160b01710000b114003c0000d078 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 915434019 1250 915432769 915432811
    0x90f021c0c09030b010f030506100305070303030b0409020d060623011b030c080f09010f03020a1e110f010209040b091e06010320070c06090521070504110c0f06 70
    0x181400c1107860301030060070040440460701d11a0710074080d020300c0c204400000d185261452500a000f4040c0b030000002400a000050001c9400c108480e05403070301080c0c04482c0741c0058000e2501000080d400041600320310208809038121108071120310340c050844806c070810200342410041007560000ea00e010040d00f6803240400003907005030084c50134809850480c0d40b00040c070b5020a0342003d4000002c100d40d45d10750307402222014031310000d02e01507080c910307210005090740b00130b1132140703401503085640614028805c00e203030644485010115044c1200304541d46000b50303c1024140d0159081c40c030710303c0480c100340003c980100001c0f40344c1c1e4568000078005a00140c0040c020324101520341e25012042103014500f80c2c40381304258085d6503035005518210301c0d04401940200203000030360000300466035440c1140a14450000302240000301000d01c207904207115070700440d50092824401c20007210040010388011120b43e0110351240340c00c0c04203541d42e69800c40303800300030700c114010f00c0c0384e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 915435269 1250 915434019 915434021
    0x10c050f0d110310090b0f0105040603051b0406180b03091c02031207080105120114070c080d150501080f01031e050a020d140d0503090d111213090f021c 67
    0x48003501d40c50000510000c8030301c4080c49603000355030191030184000418010035140e481220610720040711114000e690041c0042c2260040e031090030145940c400014103206410109050300010314945142d4440c0c485c00701901c0741709002c9803201070503048800490041110011240a801d91400804070f5070036050100b1400900414041c0460205120f0000c1d9044800c124a010750015110b1070b119604010a2125a04500e802648260705001c54281580314803104103802c10b111f0705d42440c0c3c0381c0c041d0500860901c16925005003652030112103540a41c0b40002c075201ba00e00c04d076607450341c54603030300b000d02a40d410a0001802c1d403e1303100030111850804424006800e480b82054441550103031300002c410b0703c5d030309000b07848244034841494608a0b040c042c45c01c1100c1181440c2d400c60900b08011513a500e4101030300c4090142000041d02d4035002002440134244540c0403c41e03135030000081c12081010a0311818600d1810400503803850166030003a00d003196800c1400380e07150590010480 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 915436519 1250 915435269 915435277
    0xf150c140f1603020a0f050c0906030307031d0111120a0f05070c0b090a08030c0109061b0801031205040b1605100603080a03050408090a06020307110306190908040510030b0108010602010c050f 84
    0xc06605c507803607240002880e21008030b06194003900107007a51500c4481840010380c80100014420b4000300f00c1100003d8010f15003186e80c00c0300d40c103815248042100144c91444400c1d02c582414880c1c0403c26039807442c40001400c40c4200e654a9060b5006102c006a40c40c0c050420001c1500d90b80007002d100300328182015116180d0000e000140040c0d07503007900d03811a40002c16010749a5182d003400810701015001c1c00c041c03102002034420001d03170310047c010a40f01040c0801400b02c050110450b440a02c90310aa07809400c8558459658400500404055014401007220349003d580102e840362411481108201c0f5001f40c0201e10f40144410201c001713080080044400702d200717001d03045043d02d91304801c101074291500215078512050078a190380441c0380c010503101c0d600c441c08101c00c807902c0410500c44540708000103342c40d1014a0304000d40e00440e0001c50b00845030440d40e1403a5617141d0099111840301ba2100f0420744d03200e110403405d9941d03000082c004140100060000804014010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 915437769 1250 915436519 915436523
    0x1150e040209040f0f050c0c0a06110d0c0903050f1617120d0902090f070203070f08071208060117060306061009090f0b10080708040204090f150c140f16 67
    0x140b901400038001801c0315602541c20740c40ca95a035070080151944c520545030003c803602c820f5401c0401444120340d03140e003510401841c068031500c160700402000002c0e50102c80c0300c02c0c018001c8002a030002030441007540b0081e103080c862018440080f06005c101c0b03040e045444030f1022205801c0800e40001c11400740c0895580e40301d1021100f05c04140d82c0b010340400d00c00d019020614002600400900300d40240c903101001d800032050204040d0004201d80b00313180e01c810041031009440c14220340900400401400f00758070041d6111080e64801c4000e4031815003604e94800030060041030070400042154200c1e01a40082d0200742945084c00c01540071400c640390201625440f10140c00646550106a0009503141d0788038001c249000c10320b00c22200118686051145400b00300100403035000341c00a07001e582e903481000d00b400300d40d1030300480403074201100707071100b4111812042c01064400500b40000d01e0000c40c1c40b8034030001504455200c000c80601c98107009080b922036401400d0000c003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 915439019 1250 915437769 915437771
    0xc030e030a0209071808240408210a0c02032703120d020403050f190201030216021e04050604150b0a0e0a0909150216380103050c03030301150e04 64
    0x5240010381d034040d03080d44070300c0d0550341d104412101e030442c6964100840c0c000f41203a03007000304111041445030034070105404950200c87d0890301c07107003040d6005100304c0100d10410325a240c0405c0f00c07203881040726401131301003c00070400c0d1440d68500700d840740901040c0140b55148650031301f103050741a840e2a0100000103082d038620a82001e4540c1c11540410204007040c0c0d000705040013800320900840032070300c003a840603203040c92080e9080c0c00400c41a00b0000e0605a01140030100401340d80c4c0440e00c15036014003202803d40720355012a144070301c41c404541c4a0342c00c1000140b500d0030640180629190034031880c0800300d0405104c1045900101010001c1002c008070340b000503510080b4001c001c00b10140d0020f4910790301c0c01e0040220500c012022800390040014400d25038202806020315900207e4105c40101c604161982c2510b0045480954800401034001c0b41d8a00728107081c100ca04c11000c882000c0c0002c0c0a0603285d0009100d008500b0070440d0861800302c1c0124081507440c080148 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 915440269 1250 915439019 915439033
    0x181a04020c1b0f0a090e12030f0c0d140103051e030405030d14071703012d050d02010903020405180105100533070b010611070308040618170f060c0a0c030e03 69
    0x7011404d60030050380883e05441d2180b81d29044040180704110b00380c0e0800d2a4985540390580074100c070000080d00b1031022000c0018000c5a0f0085070341300c1078081262810110003569641010703691143c400c1d0002c1902c40a40b4020b412a02c07001041310200c0d60701034085d040b548038004013a2030b5660003aa01081d54041000010006550f66640500f90440310007420707169418009800841d240b2211025420345401c0d000c11021900c0c00004000c42c0c40841d48059081011710040301e00858980c0025000b504100034000300c041001c0186007144282c6000300700c17503602c2083c070040d4645184101038000045d9400c84100d41d014003e0708581d68608161021004c0032510104440d6010380010f4400c20880d10042c4406540080c8143d02c0b00032820040546a0442d100d00350a0f1080b84130702c50910691a01c900000d28803070311100018a17a02401d0031200701613031241511a01c00c80d048000c1070041c00c001600c04d40059040d503154020941c1d450800301807641d006d4500800c0400082d0740351045013 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 915441519 1250 915440269 915440299
    0x6160c020a0f031406070e0603060310110307140403020901050f1c120f1d1009090204080c040513030c020402030402040609090c06030c1106040b10181a04020c1b 71
    0x11010070020310100340ca040e901e6186061105081070b260071a14003d400a20500c40b00343d500c4a207078454484110307100d0b13031390b6211080003e00c0c016061030345d181c0040c284114045030140700c0c000f071031064109849107a150f002c08905c04449100b980802580130b0300050042c441c604101075180305521002d0621500d00f0142596185052004101265220304058050b40400d030700c503058074045096410404030314442161110311705050f180070306006040d0a2280740f90140303d80001001091110421541c6d6512456020344810011601e40d01590502000c1854243c031031070100350079a0103540f0300729099115800c00000c0d43c000781c42684d2203903c4c1c110103e41c501c2588104100c0901c21130021810b1407034060064192a00c0c4400403090020f01c3d5190a4002c00100c2c0942e4820382c001480e9403943c0c0e0700c0b9003500c4419a140c0003c08101c2c1c1d0340702d00705c03001030740c546c41810211120f24400c0c10401c0070360104000d80c860107000710b07850380000c10080684c103802d100d40b41701c2c281d005140c0c03002d0411103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 915442769 1250 915441519 915441529
    0x20703020f07030602070201030b04140f040507050a18053102130f1d06011a13080304030803042f1c0b0901060311030102190c050c0406060906020f0d0206160c02 71
    0x43d0402e481c180d40c0090050119a014800c61110020950702840111950b0011030210352000303091202e60700280c0e0020301001001e000c2a006044001d00c2120b86945030b691211a80c194000701c0c1040501e030801044014240351504440305454010a40880d1046400c41d001205522000c98103c10030409045842170b0900405045030124600000c468050900222130410550212000d5030801070042c41000c12031150809610075828484c0d913540d04907000180b101c0c1d0580d000d1880b9000c0480c010040115400041d40258050114000701c6001012a4041440100d04082556050700d1321504c03203041800150f03080100c2c540005541102035140c4051121040350041c045942d180340600c208500200f0f01c0b41c01c0c80c41900218100b5452002030400b49040c41c180906211821001b5404c20008014001d802800640305210440e03541e000641684c649024100240c05503900020310809d00280f0100241d2640c0d004080c4d64a031150044e6024840071107003030411803103002c0f62001d0303106e03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 915444019 1250 915442769 915442783
    0x18120a12060b090316081b0d0515091c05030601030c03411302040203090f25050d0c0618032114040b04030308070c02090a0504120908060109020703020f 67
    0x1065102d991440604101421309550410550a5450800c01481100c10010f40c11134510358084011384202450720000321400400c54008019105500b0500700b100c44a90a19004102030400c0b1000258221a66201d42c40c1c1c0c141310310006541800080ca641d0b220390042c0c3d0111060b403c001902c003184620031000b500d02e008102c00e4200c09a120001d1034401141c001000c0600e801030480181401c03440c5915201c40c2c1c01c000703445182c0110108039450402d114060300c80049108442803000300701048040c0c400f1000200700c0c40d00341c4410000e03031030070402d0290070441e5100445001350340c10624256102c0d4000c0b510003849040f64600400041e10010004650401610701c49489110a110007800f03250b108402d1241082c09100c20440c5600510136242526458240800255907030342089420340c007154006548252020305011030b90720540e0100b4007403030044501c0040d5003081c40d0140c610301410302c51036119500c100010044052203a029042d264401e105075403081070aa040c851800031 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 915445269 1250 915444019 915444029
    0x7080609040f050d080105010f03020c121b0a0f050105420a060801090c020a050706050d09081b0c090903160809030601030321060e0403030902011709070e18120a1206 73
    0x460b1800601c581e49c1c000d0410582c0700903614095103131004483c015a2520b20f80705c511022043c021814620680c0d181c1c00178080f82d260401160000c24440c107004204280d0700f44241c138030354a45400b15140d102450b504520180d004809803605405210003040c0d001d588184414410282e1980d4100a680c0c0a83c0d45001f003000c1d50342c000c2c0d07550400d0b00c540200c0d688910044155270200c210900008c070080303000d20480c0d015080c4640c44000c40100b00300680b0748990010f11200f00003a004110203054400c410340030b51180c0c115000c1100340018071031113000a83e4942d62a52007070185440c11100417004040041c0b00e090514140881c4002182c546503081c0c0048012441d40c0c141c2122041c9902044030300350081e0740003031001e0303407070105950b401107400751010b401c02d038950034014190390040800c03505001907074081041318a462004561a88014010b1a01e660b5010003c01e0210310100301c000c150b0101100500b10300f0030305c04c1050314036a00c21940300c0c05102000400300c00100c01c51046100070a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 915446519 1250 915445269 915445277
    0x20a0314011409150c2203060903171b090604030203030d0e1b0d0b07030e0d091d061f02190506041208090d050f1c0b01090e07080609040f050d 63
    0x80e451110201011400810051650f481400100030560310b42d008160031107040300c4100d5880086452001d40080d4060b5000b000706610a1b00104001582e44240106030096551308082e51105280c0d00c80480d080e030711020b0003524141c02071110f180c05002040c0c941c100418503413030107540b039002c64250b4112880b070392440b41c2c0d520050034880c40705000c000208165803411800e1015240005600da903030100c00a0700502908000800050003548040c500140140c01c543d035031a4a000c0041c019255401481d21448c44075401c02c143c444016809801100018421104042c04401801100742c8060050045109054200c1c1e401d401410740d0052050082e0007a100c2454a40cd080304070700c01c024032810170021014104030880d9408240c03040b940000f480c10513610301090000c803049018601c188014405d040542940704111076022032a1103c0030b07211210354564039640201c400c40304688001c0410b58040005010340b0340310a1203580f040c40f1707001e003032046a041e899241c90503007600000c80100d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 915447769 1250 915446519 915446531
    0x219031b0e07090b1204031b05011b180513021303050102040614070b060405090f120d06050609060d0f090b04121707020a03050d060e090604030e0406030209060904020a031401 77
    0x4505103030140d40b116050801e11802890805410782e14428400040c00ca00d00c460045410580f00d800c00e00100c0844003060f038440c0080d810100d000340240802150300c20f41103400c00c0402c80c01000b01d181c0514070b59007803000d514540014007618031011000580d070b541e1f0810010001700c0340341c81d4913030155004100040c0c136a402d000001e4402203120003070100d00e80040c024200000c2840a1540d0f000400355404240394444140745407500c14960014121400345400c20305003144d07000c0c0545002c038841102072149030307624410721030284603099102e60040400c0210981e5150340fa00445002d21007400000340c0b0f0f62041d220a112450143d07401c450030b000e03002c03510001da98880760000340980c1d95502c101850500100180d0380d805007283c01400c0c0310707000c60511b0400e003269100e07070020901803d0300001403410101450310b52a00312011804940d001c1c2c0819002e00b0503201c2c64041c2c0f031f03029004400c2074403031104000c44030320014022640034003042000f03c005007003158088685e015400012640c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 915449019 1250 915447769 915447779
    0x180a051501050f1e0307080d1206050a0303020d1d190e150907111614120109030e060903160305012310051512010605040302101b0219031b 61
    0x10800c0d060344264401d03a031078104039001c2d9850144800702826018407000e403052003000403e080c0310260380000c15600400345c0782031156410401d00013210030028410003100307844404119501505000140044e400200c80c0c00071346000b1030600340500840703118003410208200c0043d03101c1e004854442d00c030807483c078410803005140c03001d155008aa0744001d107400e9071030f4901003601d6000080c4403404000951001c880d11240602c002d001000140505c6007580d40c0707a9486020103515282220300403211410706550303507034045c441d956071194199220300318401203030104a00c3c2e40014118540c035000340d40800c91100342040140004522450020130b01190003109203062510100a0f05001500402001651014101c00c0404e452040b61851a07280541655140038000d092203140c20720403d070004030b2a1500440648100e9100b202c8410040202043c1169442018501c40304641c0622102000620f00fa01d03500c01400304064100072816540c0c1c4540420500100050440305107009040c44 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 915450269 1250 915449019 915449053
    0xb010f060305070c031d01050708070503041a0f040303030c090801021803010b040c020a080f040506070c0312171305032b0c09081905010f020f2a15180a05 68
    0x90701400c6804e280c600c2251399100503204400301c00c1c8503541d000c441200306209030f014405070780b02c19800901807519048245442a665445401802150340e0f60025021040210b08111040c101250b031000b401c081c40d40c1c1e019005021f0301d1152101b880300303000300841d251109102078410346248520f0040044031400c10325085030203140f078490155007441600405290009024160b556201d03200984d41c01d0151403041c005e00035600030b2513002e40700040c1c00c814071644884007400e0b83e014081a80a80c12205400c2d1900c00c0c1013080d125075125248009401d03207030b08884080d03030680a181a03e00d011000140d8070840030408440c8101e103002c5406070100c6061038071542c030700c280341810a066264100103419585901e1000404405c204403292202008030a4218410041d225082992940c50800300c10b046e42d0000030007880090300104441d2048803004210b2081608420003512100e5003100c0a58505d0780e0081c520300290102c40d0882d44c110f03404000001490380038401a10082c601004102 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 915451519 1250 915450269 915450271
    0x1c050f0f0708060120030408070803132301080a0e0106080d09081519140a1e0c1e020a05070e0906090606100c02181f050406260a0b010f060305 63
    0x4010b4098200503099030481035060040c03d2428180c4000d80d072521074140ba5120b5900650348a0081d0b2000050030940000a400f91603003207406100d6050300c1d402081c420003606a0701007086410074810b106079502840d0001c0d0807004609003c1062a01c0105090941d540ca50241c02c031688100035072030741d00c2e81c4440c240025103944d20141c80780583d00321414000c03071000380c040480003840e20207110b44612107030700403034402c0c214401c1c02849261280004005000e64501c00c02c3c0c8480b03002102004c0340445c803407800721034866268902c0310b0042c40d400c80380030003007266184158801e005011020540c1002008002c01c1801d08585503480c00c242c0e21402d0210181c4041c1d220384c0724900741700e070a03511038681e207080d03d22525081914040ca8000180c5841d000d1080c1c501d584c1d103030310600660700b403504495001d0584200b84440e0072541e0700c05100c21030b41c0512a820108408408078600d140501800340c81c0c1144001c01c484c400b05454444009030107080c0d1101c00c49080c2c505007084002e030540145 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 915452769 1250 915451519 915451531
    0xb030105041d0d110f0105010b0a080901090209010e0c0705071403010e031207050a0909140a0e0c011218020604060f0206130f020112110d1d01060302151c050f0f 71
    0x4041100c120310b010382e54a00700c00c40c803002c2c49480248401d0104003004000708001403c80240807a5940c3c2210f141680e1041e107003400010b041000180c40881c05001c2d1504280d800380000240fa1301e014540010030710701402e034a010302400c0180d82c0100781c040080b0805840201c40c0746100000c01010182110420780c0b1078450380d001440024442442c410410fa4407181c68106183c1c1c84982c51011103d0200c0e54014801f01450820b200400c040601070203881443c0209017000030440008005a4499442d0300311400941550755882140d4907540182000f4001c0b01c80742202d0341010750003d00c1c01e40040e000b000001c0c140c1c0c1404507a0326410810a0303004807400080303007600304050f01d40802d103007030540b8080e06019680a460710301e400c40c0c0e401905118403685a0340d4940c00c0c0002e0050151002d40307084841c0c50b4112981c10810302c41032207051304a83d4000c1801c00038405580c2184503940244042040329040400000d200495a000701c511547c005011a485460000c808031b05c19000a0f083d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 915454019 1250 915452769 915452801
    0xc150609040f080a030b0a0905070e0306010b09010e0409080a0f18050a05040504050a0501060b0406021b061b120a090918050d05090d1a0106021905072d0b03010504 72
    0x500011030292410000c080790800383e000e41c0c46403050420380142401c0c0c3c1d000c0d500a9182d00c80001c05401e40c0c0e0041e40220300c1507440d4660308058504150342d40d0001e01600d80411010020540298013521409644c048080c001081c0d49015071203403e01074100c5039000c00400c98040000d44030903440f4202c40d40c24985028083c1d1800d0900b00840d101155034080c00d800f59644d0008a818000104848064030703601a00330300c901030b110a1013400d00d0b00f10303200d00c2025101d000c08410311480b921301c11010307015002d054241041109214403000004041400900d401201d0410b404062320341c009203c0c10710340d900c031107005600c0c0a42d4842101d080300d07801207c10445001c0c1070001207000c070780d5a62283d0140340850303c8603000400520300420515000300206011094114515503941c003c5040b2401c640030b454010111003124400c11345580c1f00105030740c026410034803081403032809940848906680103031070400070801350081c21685030000ea1510310084010491071420b4010b0541d461400c80c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 915455269 1250 915454019 915454021
    0x30f0106030618020f0c06010311040c08041e08120916080a0c03141207050c030609060f160e03011505101d0603092e0c0807080f0702120c150609 64
    0x9a00c10202a08808030500c4980011741015401044000e50300c062448500703071025035070759180c18400114050a00c600560034160254201400381d01014481d5070003203e0420742070079020070390806400c0d940d41101d484205000c5840d96104190f240d61288403000000c081c3c2440e04244040011159484818250b1190800c0000104655015400c69511100088240c000e2a0307081e41460f08030014105558004280c01c3c0c14014006a15200c15a041d4141c80f0300b41c440512464407074000301c0f00650804c1e00d00010400650b032036000c090600b0300d1460110300780c0c1b1801d0002429610621021001404910810f1150f0720780704503441003031030060600301021143d40e01185450b042081126110304030100002d100d1400512201207150b16000308201b1100d01203019150041c484800031100030300d852800308060b4028230314103000d14000d0301d4000103540c851801c22803491b070082024003107001d03c8511803034a5040101802a40395004054a044403040c0300d0401e035940d000300035500c540c0c0004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 915456519 1250 915455269 915455279
    0x501080606070302030d09081903050103060e0f0a0f0602130806040b1614090f030a0311010c0503192318100c050f07110a120302011b050405010e0d060f02030f01060306 74
    0x1700315a03450b18001c201017960301701410715050358003034184030200103a54483c1403812141c0c140c3c0030b01d06032803148204025074103103083e850f80d03074001d511400c840c1e640c00001203001181e2540c0040415a120f40005031030000080c030304803d034492540c8051410b034820400d1008000450000907404424000300c0c0b0705c4200d4003000100010302091045030342071030005407518a6154000c40b80c141c0392014084602d107051514008042048540356180350354a41190744181d1880f03001182e01840079208440303441000c0c2c03030082d4000c002c1c0901076800480d5008100451000b0804a00d1246003500d81211010f8102c08209040a040c140704a40c000d1411100c1d50205405c02c1c195144001a40046a00c4d40c2c0799240c400c4031410b040d220301e41e209103400f500040000041c540c100c45240302b40d00a100d804400e081251b00b0900d90728107a80454820302051290394170813111200b9000b8020325180f4101e01d140c03101002c5030b2030179541d8042e040d000010000b07045504005280189500c1c82d08001a52510f = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 915457769 1250 915456519 915456523
    0x8040f0303110c092a0f19080c09040b060c0f1c090b0307031d06040f0c0e06130c200a05060c0a0816030b031510050414060d020303070803040303060501080606070302 73
    0x1170101d1207541030301502070310109090f01603042012082070400c1e5214201c801d4a00c02d034100c4101890040c0f09902c015030001d104054203809250200c00082c1018007650802010302601d500311074002205124000c1c00711070402c2000300480300ea2001e044505107450400c540981420f020205115045e102044031014480440350300c554a4900090906456102661843e082c10142e01d400d110304010b2000f8401c440d00f41b0101301d1b10600715000c12590b19032200d46a0321003160080d03442a42c41c01218600f060310342088191440c640740005141c41c441c8240c071411000c1e400c1c0704245520800c40d290802c0020050b11303810481007000281030000400c4028204d04c2d0060403907811715021040a01064040d400402036090020151a10020f46000b07102c64900300300c0d40003428010301413002449003068820781112554031265007403950341d0305003403001d100c1c41400c0498161000304900404607000c0006140298425500400c000b480c207000144404406444c5605c56081006820000707900 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 915459019 1250 915457769 915457771
    0x10c020609060a091a1c0c0309201e010c03032409020c0105070c0203060a0b03011b051c050603031b12030f0403020d02010225020d02041104080f030406050405190308040f0303110c09 80
    0x4806c0000c43c040340d000700100c0291405180060070010324286100c81c410041181700e280c0481a01e1034211703444020f200c030300e40c40f44919a11307000c90781c82000200407903c82d401031148501c0e8005103851820304003d00d1540a80320740e0158250950110314000c41000138001d458000b122883c0010070b4030181e4001030746901011304081c0b03034281d80e82d40b890740a4500703401010804c0103d0041008184030080083c10507800302e01c05441c0991012202d55507079100c8d00c1441e00869011380158104580e040505100e410b002285002030312a56603603a00c040380040c011442010607440c0d0310810b04052401030b01d01080303101c080d010740e40103201c14160441c80c209511040400c8144c80349030080c1500114280007825840690424104411244610328050007441250040001c07207000550b02e104e00c60b243d001c2c500031800096410041002585450b2102219540c40c1e1606001c519581e56540c55045c1c0c0f2940c80b1018040c250b402c01c20074181c100c6003002c07903100d550015055240c202c0d8001460990 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 915460269 1250 915459019 915459067
    0x1806020109150c09270c0e0f010f05040b0f04170102070c080c1806011b0b070e0307051003051f060206060a1d011a1201030c031707080306010c020609060a091a 70
    0x1d00307036030f41884589204401c0300b061701400a040100c4290b0080040c107151550800300c1c05082c445510b1111944540c071213103a2900c0c03c0d6504d42c102424030b51440c580d580301d001c40d900541014040880c0b10040358030540e0941c602c60000581d2600507140c110340a660340d50041c00e55811111f54006d03581c403607006038103004480c04001c80720b030390743e0100503103a10031005040d02050f0180d0060b401040711301a4103a008002c192100542c151080c2c0c00c142d6108014002ca5420420107141203000354041e0f0400e54228250408480c0500c40b682014400d14a1a522280c0181c0c03025003845a542002005000a0f012001c400803404420b6a40c91515030704c10310888001c4a19208160102c090210030740d0b0507906120304008580d40c1d2401c142c45200842e002c25544004800f0038400300c0f1a4200031581c107143e11115807415a5515001501d50305001801a030b04503c040100d9030450f5100d100a150481060b02c83c551400e00744800c91a91091003c0c03140b0341540204000070900003a2460172000c06 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 915461519 1250 915460269 915460289
    0x706151509141c0f0b04140705030a02121f020d0b011407030f03110c0a060e0312130c050d030807030b0303090a0e1504090312050709241806020109150c09 68
    0x80f64507280111031000d140c00f402007800764181e80b04000004003210300a600400c070790491710095580b41a200c02152043c0c5906601c081c00900040c1408000c1c1c110505003c826140945103000842c0718201c0802d000300506031740003d141c1d001c040c2a11a0f108464403e1a1003801081065a4254280b2400e00c001d401c0c4a03002c0e00030301d4402d10942008014070200b001041c0c0b074022400d20250764580f0028201e484605000c0101c00c0c8140000544a8010f035000301140c4a840c0c0d00f0303050f000e524502400b9604196104808241611103880440b03419200307a94401c0e41c0d02d40524000c04840304611042c1c401c1e003041090715842c1e60b5449031481500c60704110b408080d04c4200b41282c02d6601e042c12260020309100802090680220b18031503c0b40c05014248195510307810122003000d00f60280f02029404d40b0707141e9881280c041c00404401241d030034180c040b200d0940c82c0d1048036250740d102d800140e4484100c482003200c1c41136a0391064440380c0050011000e285400741c41103a05025801002e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 915462769 1250 915461519 915461539
    0x40b16120e120a03020405010306050f150c07081209091008030a14070c090902180408030106050306010512042a0b0f03100306020a0c020f09060f090a02070615150914 73
    0x2201c030901a01c140e040c4600c1c20103030384003406440034000e5000752291a0109160040018050404981200d074515004000f6585805000480322140d0825170041400388100340e808140c1c0c103001c2000c101e008420320311550312411740c0f80170005140c40c020103500c520312140381c080000c1007002055580d11300b00ea080c2180d04007600c1d05035800c54001c91601401d00c07240324000180700340295016051031030003a50810440c9030020400509100b05940080c07660390304000411006200d4409503400150514140b80341200010310b0202c0c0b80025101907403880b43c0020275030070b80680c6010755008203030607100c154580340c980412000d40340203130740101000950000007c0e001c0b0301748030f03552070103542c1c0304004540301c00ba0002c3c000d0003684510800c07801002e1807004d0f2802450100c10b590303c2078030010803c80d0558590700c00d04c9003d94002c2c00d15100d0729001d00441001921074000c01ea480e050002c0350069140c81d004207114514000c42c008802d04c103940105001007500c102140c0f140c0030058801d4411 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 915464019 1250 915462769 915462791
    0xa15090b130209360f0712090602040504021308010605030a0201020705101803050313051c030c031e020309031207031b0203100e010902030f010c0516020f18040b1612 73
    0xf207654503611612210508005102e00081d1001c110300c4c01442680603001030740c4440904011072415940080410040e18101e00b806041c0d8101d0b22a01e8072610016003440e6036a00894182d800484802c020000a04028400700009128000081c4003c42c024242d01449800203911108240149802480741d64040703561507000e107012554280741d40c41c082c219241d07130b424803e40700d0300201420b11045501000005c0c00b8a4900800d00000c5c275124602d81c06030000341d605480020001d1000c40c01c2c00640d03029850700c840843c20f030381c21250702e98000d03503034602c64003080500b4030480006580048200f4490500801e9004610040070204404000c141040600000303142c48003c180f41c1a140c0c4c2444003200705c14506411107426184240d04554030151200c407003d00382c2e40f041702004005601400520b40f0703403440d441240d10309400a0204011411b02c100400c0d03081d07411502804c05050010180f01c09c0040030004260b0020002807a50002840b440300207040c0803901c0e51f40009075417030b50400c0f01 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 915465269 1250 915464019 915464029
    0xc0f020406080604050a06231609081c080f0108030304170705070906060807022a010c12050325050a0f0e120d200c21060a15090b130209 60
    0x201030b00078401140c07914607041c80c1166030b41066042c226041c0d810310b11031380081c5011203000748800145691142041e91420b42107140da0a0b1140c054040044554001032942030520101480c540445070b2441480701006024001a5010b04401850100d200041024050200540313821aa10160a28112010b10039403002e5000c0c01602604900420fa00001e003807802e688080202d44440d1a5007040d540d446c402a61a003c9041f04104105040824101d01012004040002c088141003c201a00c016202c0528241c24920440041540002804030340600c0f10715a0400700c006d40e03070418500f41101c000625030f000c0d0400210503c440307145030b0440c15010351044000307500c0141c40402c0c858040000d03243e840c448004418049001030485602c005d101081c8010305d000440000c4c20854504d07820700000da02e416402c56440c800483c440444041d06000c143e009008040000c9241c904440d021201c140b11503020441051918015203860388540f030030300700a039511250050704c502c52400854 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 915466519 1250 915465269 915465281
    0xf08011206021614010207061406030a0b060a12060f110406090b09010504120605010e180c060f0705100912050304021e060903121b07050603180c04050a0207031e0c0f0204 75
    0x208114071401310300c00001415030241c90600d01030407081c001c00c0b55004070b03008004410b68601d41c01d500480704620110383c284440a40201000d840c41405035070b00c1c048a020135000b804201d803d1501c808000c002916240070380c0b2503070030002107803d00c0c003031400c20080c0c2100602d2042a034080300c0451078817802d0703020304140d0b0014000c1c10715601b039a0f00c29103022401132109014003001050707504041262107504035a8202140d441100615404898130204100c2d600151044d0800d003c04011904c00140240441600c24554510100d102005440c150681005900007001041f80900030000540c1e4cc81902c080400303500310b50301641b10014800b01d81d45214104a2a03018801e0703880040d601800f400082000c2d6001005032282d0420101106445500c05d21031241c0c42203003070000c1004a40304842d256403004001c4101c454480040c000305003035560850300310321000d03070104118051503001740900c0e850059164401c1040c0c140d1100191071649061000380181c180e2028a6045454a9000e9 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 915467625 1106 915466519 915466523
    0xa031103120f0a110321040b010605070c05060309010b04060b040e090a020102030a05030c091c030831030302070c141c0305030708070c210f080112060216 68
    0x403203135070704d403080718400e6400100304807941000c680c3c43d00940d4a103814611005894035003408004448140c0c4080e0038001d04001c031400159103010383d0340640700304581e0942c0325151500c0c02401852441c0301b064004e407070b02c0700c0850341d6008200600b084580340418103e02e950782402064480d401003e000b405a403007806008402e502800c040c41c0d02041041d003490401c81140c00003040c0440301a1074a112801082640003030590104a65034007178034920a64002c83d00a2020400c60b540381c10603200022a1054050200351103601269030054004126103c0300e0b13100c40d07000407418040c909461250444d110321000f190f070921000f0000c03030b4050b00e40c42e0450340c904209a41750342000300f681c42000f681554060005802c002002003c5074006d06040340f0048800010301030120030b49a26041c07103c104010000001604044004903501150150321000203200028040341c0300540 = true := by decide +kernel

theorem cover : BRFrame.Cov 915287769 915467625 := by
  have h0 := BRFrame.cov_init 915287769
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915287769 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 915287769 ≤ n) (h2 : n < 915467625) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
