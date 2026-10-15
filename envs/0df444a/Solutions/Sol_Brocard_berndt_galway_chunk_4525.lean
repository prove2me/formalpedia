-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4525
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:53:58.95767+00:00
-- url     : https://prove2.me/submissions/620ae081-f52a-4fd6-bcf1-0f20eb913b76

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 813669064 ≤ n < 813848920 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 813670314 1250 813669064 813669083
    0xa0308090a0302043608120c09180109050a090206031909021503011815030201050703020a0c181a0303070f08040e07050a0305070309231006090e060606040b07 70
    0x200032501c039001d50740009400c0381c0b8080c07030000100448132034a84982e07080c0030b0030407008103c00309141700444628002050349000b0b00100211522414103140d000b000e08810900f091002000039241000450288812102080040c00b0380100340c0140d9610a01c42c05040c03103850b501e540030030042d11009085402c08000d006030a1024840c940041041c140c000f0100d03072011414610b00c0328168020301c81c03c07108007000f07076540006081900a0780c4100c030880a0000c0041d1440e00159000c0d40800320440c01c6020380c2c2900400141c214850f00090441040300e070b21424400c2c0310354011503298070060075905084211112030381d900001224240c551009078204213240501e0800c209000d01d800540c09407900c8c8080201180d0b028000e000302c084223544c140320382d8032544415000c0f034441c1351010f403100016103001035403005048000545103c82800b194151500354204000300e0b181d54020f20002503c440076401c008070108483c640101d0b0444903903282c83d00e040050441403203501002007988a0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 813671564 1250 813670314 813670327
    0x80906070503060613090609051e34020703140f0c0f040e06070e09010905070c02210703141204080601061107050a180501150e0904020d120c031202090a0308 69
    0x141d50045e01c5040720ba5000c5444141c0c0c8400c0301002a04a0340078a1911a1520b40050302541c407015407000c02c02c1c00a200483c254483d802c5030204030729034111142864103002444001405402940380c80c0d02c041d030b03025117603041c04c5282072407072504c002c04100029444915108070100d00855490f0801108540180003d5030740e002090241c204082c00c1c0303004d07002d00020003000540009000c00d40700d000326501d00c1035a80300d1100d0000c40b40c1c01c0e1007107000600d00f50500342c01410506a4910304206400340c00950354290280586003680030380007101c0c0c900c4604451000d0074010420351010401c44074582c0e08103820320415642d10f02c0140710b8481005034101c40f0a4441006020b003c000c4c2a01078001140c0a03210444002c24200c8110a9000b0900c0c0100014440070801c01c941c460784403590b1100000701d826230400006800c003800c01da0b8030104401c003c40004108000b02001b198807a00c3c2c4100d003100504002e80a81c2c40d2510507401a8010040540141d031600549402d44e0f6104900325120741 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 813672814 1250 813671564 813671569
    0x10e0312042601091511041805180f010b0423271005011404060f12020a09061706070206060315041e140c0415090506010c05031603090608090607050306 67
    0x34902d4030640b2951a2007084820300049803a403c0201c00041400e1240c500700c1d01410804d07205170321410405480400180c501d103603032904015046510240b054101540010045040c25002b01f4040f445130342d40d4070030844c00c0c00d250061041c2c20741480404c081a2101c1858001025401010741d51440d540c0c134a0384040002c0803604d017600740c2c803200c1240c0340c0740d1024000d00020a401c1c0214981c04404003401015071605000c2d003000c0d00c80030842907408621349400340780b0b4a805032000701c0e4020720305c010120707841304d6034400c40000344583c40c001d40b00c0b110b02043c102d0030800d000e008001190001c00400056440c0003c45182007a901420b192089e41c450901a441445607400411040c2a4030582d00c140041040048420b10303114050b2a5034603036503403c200454140b0369000007016200f483c100490803540c2e01041cac0c8140b044c14031445017070300303540d49a0540e80a8444001034001c400028403c1c198080c8032a005006c4a0804100307c0c2854103e55a40d0b4000070132100801100000058268 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 813674064 1250 813672814 813672869
    0x9090f02090415050103030309020f0436020303030a02030a0e030408060f0411180103020a1d060f01020106050a1805061203031801060b040b030118110415020c130b010e031204 77
    0x54402e500404c820b584070318004000d84101c100682c0300c0d011100b8031040c035183c18810209001d42e00388010003840c0c12140340c1440801c1c50414200004405142080507072030500003988248220500184d8274540599198119044442d030b2011940c02130205210040300040c2544d000002178081e0002d40d5518907201000390040034419810001301f8006c0c001e601a2484a2410380c0d00c03c03070381c0002254840d00342c26002e01d0702c4d008030b200e00c5500b000410b106080040d0443c44420040c800403401c1c68650f40030423429100c90784a03034411018000c051340341b9069403040b143c0000d803c85625410240e00d80440e541e0340070240c00303103103403c09044080e42100d4095200b10010031140c2050b43c3c513a5074510070382141d81c00902c1801d02201c40c1c8819191401018442c1c0b2214129510201d401d090400c900c0c0030805005881020552280c9080190140d40d030132420781c044403110341c000c1070312050140014400c01400d000d0600030340c0411030707451480380010156000c0c0c5111346404120354100c4541d07901d41 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 813675314 1250 813674064 813674093
    0x31d070302090114040b151206031605092e06020d02030403020604030b102105010b100f05031e16020d0305060f060a031d0129010503010e0606070203010c050a02010609090f020904 79
    0x4101400035204a41240501500640c41d0b0000f07014042d40c0c2711814551121412000c0c50080101c0031418003840c6454560143c001250f0052041030042d40f80e05052079010800c00c525017100000e004020b1654100521030303500b400c0e4030255003013a1642d80803403641d00a9000040840560000040d03001c0b0b0300e40b000704020003c85201e00500701c2c40d400b584049080324013040e9003d5081a407190510f052502042c040c0308250350301c47d00d20100868040760260002703040040c41c008440c0b1007003690b0b41c5c0d03070003000d0290fa80c540e840c4401c00c0803d000a0301e89140c6003402c2c030516051808101c0030b81d940b039a01640880c400c4d1103440d52004010360460041600c084030700145011207400003a80e80c0b05620541028010000700c460203481c42a03160455801003d00c2d41c001041000180001007500350455041b6901a20007802e003142d0b940001d09456003820254001400800c03072161103035090003902c00034106400200103d0040c0d84800c0588413050001031f02900c00840814204016075240401 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 813676564 1250 813675314 813675319
    0x10f120b1b0d0c081902090d02060a0c0f030203042303100c090b120a360c0518090d0f0c08032e05011d030d030e0c040c031d070302090114040b 63
    0x10700c142a4a01605401c405c0d10f81c20659485400c5140b810039a43c800c41d140b102004101a508101613400c11026903c2515804200008000c8280c0000c10600804031510b21940117076884509002c6501c842c00341030310001c59180d00b8103500305d1700d645000c0307207951840d0b024100200b8403007400780c0c040e00c01030715652103c03c4207100003614446000d203d003034081c012001401d007071020583c0d081c103252100040d168040c82c0b1b001d4015165002c1c0118400b00044c030380c8154140a80c4e00ea0320790001d54490003084401020701e1048040005844041c480311005aa950a04c1c0d030400c880042e005240c4091190001e10000300003012400a0350b40303c140c0141000c00c2c2900703500234010041150000700d000c0c4206400704806c01c008100385601007000d4a81c481019005221052200030114050000400700580d039001c0d1015841c00c544071402075010051480e02c0108800752540c4074000003450000441049401840042c001a034603503540ca811185d40d05101340c1c1c04407500c4000350040601c03600a40c0d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 813677814 1250 813676564 813676571
    0x2103090b0f0c0d030504120c020d15020901030b040e191e0f0c09062d030203060c0408070b07080f0f041d04030e040e060115020a080a08010f120b1b0d 66
    0x80714010440001c2503101c03090800d40c3c0c80401c040000b42d05542080d900248010300c8075100e45861489141040c1907203000510030102c400d0b640e00c42c2c880300034500b400c96103850b800040c800b0701544c1502071001040d070142c0b0204005000416025292010002a580c62004140e003210900000a0300c031940b50311614a08403081d56649040007082589050494070784021000014003824113224400c01c82e80142070707118090101c2c4011020041540320b441014454040c1c0200250b181044414480c4400710002c1d540c0c1e600b81481c4d24030305842e5500150351004100300c6040094454425902401c2c505c2c0449a15030240384001c4145008a80108038050340320705000411a5030000b20a02440c040d4452414106610091105403858001140c903580d01800040004500710300d88080c90402c544107031650b41945a0b01d591560f4001c52690340090b20903001806000d45c10388601c03005242d00054a00301441542e2440745c0035200030089400c806507429001c0310024403100729a40081d060074100b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 813679064 1250 813677814 813677827
    0x305130807030c150906050702040e0a080322050c060a0c0f0302011416090302061804020706090308090a150b1f020f07090612022704030201020409050c042103090b 72
    0xc0c0d58a00e50340c80191000026500c00194802c0200c3d045030100085607141e40035141001c00644196004080890700181da8200d5203031400018030080030098032440580b640e0b420a41883d03071140c4001003800352110180c02e4020005440069001c8001a050f103491380c440038492400e0b00d28075141080a052a64000640303810158107600c0303482c105100f09100c0790705898076010b0405050038842500081450300205101529002d4040e00c42e49001d80c103003007401030840012400707a8220940444150b501d440401c01050f0300042e4581d48262040010424003000d07484800e00710064500348040c4a0f511942d411007902c410350500725810740b404041f201100480320013580c808001e40122403600030700c6c03c041186c00a0303002c2e400440700803200b0200d1444082e000c1190444555044410000c2c8540004010310b044002640c4118040d80005803030700d1a0403a02c0003a41c00050100082c42e0042205100314444143c047d040c80c014882c980c90314400b64a029030ba80b000c1034103d0001c030300340030406 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 813680314 1250 813679064 813679079
    0x1905010c110d051207030216030203101e0e0c03010b0411030a05060105040306110c120301080d03020306032d0d080c03070516020a17100204080d0f020705040f050f0f06090a09030513 80
    0x209517441c0f05c0d034201c521220b00d60b100085501403500000b9419001948003000681980d08000d194010030109400c614010324102000c0383c008040c0e40190340c0040b9115000e0b40390a210f5261200b60540c3d003440182c03203210743c01c000740c032004000c144c0a95464000c1140399110b41d00b80c0d409103a205404020054410392880e466400c0005480e200b0310482c5010580320000d50140d82c1211480c800400d911240648150040d410042500f43c0611900a465000704200411003510b00807001c541415120259400f90a041400e41d102e018000c3c0c641c240701c2100303c2ca804503688400d0b075140c00d40e2a520381c80c2212000300000b0303801940c46141040c0118295809540030360360003040d102107910b240d038200340350f8060380100c6c0300710401034006d0045000d0250241c010b60011190f588196811b8030785400008040b981c40d400e010503030035a60003c2003081f0fa009041d00d50010007020002c0520b140c03580008195090040c00305403055110306d08001007502510940d01000c00c0491206401c41d181c415 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 813681564 1250 813680314 813680317
    0xc071a0301090b010c02090c07020409020d120908030c0c101205090123060f0418060509060105040b0303120c0f0f040b18061e160618021905010c110d0512 68
    0x25002d5042d140018010700756014a9907104129400b0780082d04981e83c15881017003e0b085000140d0700540c958140e500142d5a501c05004085d114580401140b00b001100407d14100c0c0d03000340c0c6165004014006982100060100901f40101d4007144214060b500844400307210b80b0307500303000034149800d00480001c190082c0d190b00c0c900000035664645040b1b80d0003450b07501914101d4000b8034869a0106509250304026400c0c950040d2601864000d584c0e600704a507000c0b2680680c5421402c01031010f0324103406034441d200c0c0e04400641c140240c01c200c1c2c1c2c0d8040300180c242d05461400142d420070b843ca1a000b40c4284041418040d52103030780c0d501c2d040105a100c54508407404688005400307007841c18405458140e0629401411820146160480140c0c040750030044840da4007000000012094040d03050603041d620140310201400740706102c108180c05a00319999494800180a940d80c440c11500310260080d80c0485200c5a21000c0380d8070030741c0c0d4000500540030340461400150348810 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 813682814 1250 813681564 813681569
    0x70c050919180b1b091206040b160f0e0a0515040e010506070b070806060d0f09170a022e0204031b0b04050a060f110712031d10050c071a0301 62
    0x301c0a0001d10b0100020451507054840002c2c186500940131541000402c241c0c010303101c521100301031900031034000161003071000040a01d1241d00c0b0f04d040008004440c0910360308491003c1c41c1070008000c0c00350103010043e5604041040044813124002c05039100c00caa1030080002070640b1030503030800c0b03240100640c0a405102c1c01100540f000040e142402e0080740c0c0195005011740030076031903807581120340e0240581a95806001070014400c60b910358451402c0d02c449100c03000481d0001c0f0f00d01200300d90086049104012410b0129019054001c1040442e68904000882c3d0044c6508000203206030b080440d1a03140b0320216010040000b022030b0380205540740c1809401c8c00d9a100c020240d24820b900a040e08810406010080e11380903e05c59200c01d0a64180104580c6a41400900c1c159083c0d03c814414590341940f0400d168101d1120394000f40340c01a01c01300125180c000c10320071384003d00030f903040040000385100840340500c405400341400e0300300c01641c1091807613803210759002070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 813684064 1250 813682814 813682861
    0x1e04060b040b041d040804031e02040f02040602010b0d0308060f0d051002130f03050325051f0b030f07060509030f0d02011b02010b0d081c0908120702060405070506070c0509 76
    0x91440e4088403294013502446560b10181d507614046c199a02c3c0226000000365645030a0485915480140d66030301454160f2075011a006803141d20b0b051000f0f007942c4000d0b0b0b030300f0700640411500744046648407900c0f83e4030420a0b110764880b1b81611001c00c086000c03c00028000b030284048014000340a50002c107081c4110540d4000901d0300c95001039100421440000c0c02980104420303052201300c01294840c440b80313403d0344c101219040e206c850410110491080110040c03102c40c21842c460b0b0b00c0707020000301080d4002c0c104001d5240740070740d40f00c9031400b40320244880810300c40c0640d80c041142019501c99041a50381400e05071001034003808407544540380c5000c104400c10111841403150001c440002040305842c0c00541c1c403a0500382d0b110420a9061101080780782c084c0340b800f07000c1c0e442524404c0e4401ca0303442115814540b0b012101400791421074000341d080c8008108000b5800c4280c0300110707041503403100340c0e281c02844a8569406290031079911001c00c400401e8135000741c1c1e0042c0d00c1c0c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 813685314 1250 813684064 813684089
    0x31f05070f1403040308070c06020a03051909230c03070603140703020a08150f0a0e0a060b03091c05040e07121a0a0b071502070c03110a051e04060b040b04 68
    0x8070060302c5095002c11049000c41d400d00003d80440c3c803444800c1c0c0c015072203003049010541c00b030301c0b00001c0e43d20407040031011139240c00504c10850b00d24803894856400250301001110916913400c220540c0180714080d407c002104100740c442c0007800082030f00000201140d44041e030b41c41024010700602048160100c0755840001c41e840d0290007100d4001e07009568403140c50303989000e0804403010308020ba5410034503540e0f65280e01c0e2900d5180c0d001414141c1c40e000e80d20b10b080e03000c000668240d0342244800000078024890b00f035000181c0f0517004120840c0148a04200802c115040d000315800349071001c0303c45083c80030341c1d07800003140c504082c60590b0a00008d18800c1500d148801c280000d60740203002e490b82000b483c3c0d0880c020304040f070300c104007400c080c01c0744000e01030a0741c00c0000e050f646410b251604004110415404207100c07403080e2200103c0c3c80c90100021000560f80c541200c181030080c0003080e00795101c1e03120202400c074022685d5240c584036a904001034120b4012141d1407400c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 813686564 1250 813685314 813685337
    0xd0f06180c05030c0405100207051203090909070509010302090406090b0406060303020609010c1b02031f020a1722050312160e031204120c0b04120b0105100815031f0507 74
    0x400c82c200c910810701d100803070340707014948418061240c00c0d49500a0031409030ba0001708844e40c0c0c5032418070000034244000c1d900d8001d550100703c07642e000580500c0080d44550000c00c010f896001c00b050440c0e80441c4c000ca11a50b860804c840039200b0424002c01c3c0919000030801009940d84c0701c4001c0d40d02943c02c030f40d0150340e10100306080b603000d801443c020600c2e81d00384043e4540c0520429a80601c098281c44c0181d0f6420f078041a03400d54245d107011065004100c4c14041030f80000445a4032007940310180325404c103c620300004100384e280341158036a034031102001707001e000c208490b03060650317210000e000d141209807072100040c464880000940c01c004145281d140016054070000c038012440c1c0d25040c0b50014080112201010480f45a40800c01c000f070106030303142c0a400200700321030416043c14200c0ca043c21080a058020a2140800d040380000d5243e01c0302c40076500000300340b66200307200b0030100003c2c50003403483c0550751181285c84484013031721180d8002c4d50054281b602c030600c100d80c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 813687814 1250 813686564 813686567
    0x3c030b01150c050a0210050906030a05040b070c0b0a1802061201090f020403020102030d2f030a11030c09012304060306050301050106091d1003080d0504050d030b150d0f06180c 77
    0x294915005083c030b030300655416000d450182191000d04600e0f043c024500900e1130082401c5070170483c1c04501c100c1d0381d001004184100c1801c0b0a900003118130300000e03216800c0da20119400350103401d90b0082550b0700c80804282c00e40e11442e4550503001042d0304c1d2107141c00030700c0c41c0e6905000d02a1841e21802d1078401e1181140900a8506030395050b0041d6050072040b0104d24010322100850080d41401c6201700784400a00000000c5030081203030342c10b540c03031410443d88030035511444980344030480c00300104001509014140c50000d01c0c00d2070b141c441e00100054541d440d0000a244004540300014005009a0540e000c01c1c100d8000340d00910042c1e07a00c031002c0d107807a00503200710240281401d40c0f03103000004e10181158020640404002d00903220b07220b1f040c01d600004c00303c40c2d820382d4039401d1000703101e02002002400c10721450705119100d4208041140c42d840440d00c104e11100201760618400450f1700804048a0361410801000d6a201e4000c0403900410440c01c00d00c919000300700d0a420b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 813689064 1250 813687814 813687827
    0x30310060906020c0411130806070f0f0f080601020f010c020106080118050d1107080607210b060a0f170403020102120c131401120908040f050306013c030b0115 70
    0x581840d00030f02510411031085c070014181c0c6580c43c0d603060508000e10f04094801d421020060328a540061a461500040203040305c02141d0011051280409010180c5640128400000d0440d4604010191628401030f458245c7d61403490700a5428000e03071003580d581c1503100d4022034030000c00038404154000440f65140220050140049d00b254002c0702c2e11034000e40c2e40e4031564107158201c5140590b102c001354100b500075924140019080c0c2483c8801441440361004103c9c0c80344001c00140b201000007551174031403a01d02e0010302041505100c90b55006121045214072031700c1c44404286000d1a00030b000b940580003010300a0b040c480030510301c6034003c00380d42140100c185d2000f603140c24900a015218002d001d8181003040e5088020400030b01ca0180c010382e02c1c0704e00342d029201c50400000c94030352000c4d604854003a034881c1004102815056030030f4034480400d065480186a058464000302c03c240c046035649070a403441c000401c100344a480d4038102c400210242e031600c40c12103000c9804 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 813690314 1250 813689064 813689069
    0x60117091005061305010306020702090901020901120b0f12060403030606080108070506070638040b0906130b03070b0a0e0405010605090f0102070518060f03060709030f08040302060301080303100609 87
    0x1103a1004101e03080d406101d034001500010000c01241c503507640140d8400503904260012501650081604000c50520a41140d00015810001e60400c1013480000301000c06d071441e10000191520428240d41d1644103005074048000380c500340031241c6607204941c0d00c00c010f440c01c0300084c0c944030000464600c2410b5490603115110007903c401c5141004000c90740d0092030003902c000b60340d0f00c0c8110342c421064940000780c44031406810009054080ca40c004542030302164cc0c01141031206817501035803490318260748081c0071900c0403c035040001541008101440c080c640503c10040082800c401c03e1001c1e181d2600c00303585181d840e040745c109000c2a140300780b1500d80498802d00002c5a245030940840341a00300620403202502daa460000303813a03a880e020054503001c9960140032050a000c071584000ca0410360082240d8203207120014200c409510020301414a1003108000304060001141c1c01990000e0280b0b40301d5840b1204031b52203500913507001121151100c0000b90f001e015040007000c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 813691564 1250 813690314 813690331
    0x1406030c03012703090b03150a050f03031605030f16060e0a0809041e0501090e060a06030c05100903020411030f071e11031603050a230f0c0a050a0605060117 69
    0x1800003034500040d0001c40c100b8044044c1726032180e0106082200710082c2d80704072465800100003409032000d1103074808039500321b10301680c2d080b000b03c1100c0d2030010403a440140c0034194400401c4481c10003505500608040380d14046001030441c01401c0c40503500540700b0302581081000c52801d13248140d95018400c0c008286103418010a035546c50298882407528450a200e1041030f2031114160040b100e098120441c000c0d42c94041c44182d1404002c0187d1104c220902080300301d055440b040c00e8200c4a2043c20b201c0c5804260109103103202e80e80300801940d010380140181d03801c00f0f8480345240c20403203c410352400c6000004060502c5030706103485c5100e00d00e52136082c0c203040c80001c0711064203030b0030ba144461108000a42048909140105496002e03641d0240c40c0d0340c1d2048018861051030a01e601b040c0e1440c1c880491000c40c80003101c070310340c5045507002d58884d464440d407824440000c50151071801010001003c0c0070a68010034810b030000d07610340d0300142c070000301a03494520958002c0f0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 813692814 1250 813691564 813691601
    0x1a07030e04050606160830060415080a03050301051206151c0534080d08071709150c0a0912020319030e010207060507020f09040201050c011406030c0301 67
    0x112241000e07071140340c000350040c1c101481c064a11805110074041741e00304031a90b90300020591250004050b0350000d980d6102e40b80c00c40e000c6040d164003861107010b06010307c40ca554020003d82044400c0d00f4800911101050b03a12030110b5045c0504160070034490180a03410b0914111903202001c10700380c1c441d40380386c107108204903501c100f03000c80e05c220500081e0744404c3c1e1000a4000c0703a01001482d11014100b09548a05a20408010707602130404c038500070045144078092010040c045910000400140b405014607a44e06000b20f402d984454841a81d4400f00011f20034504400b00348110384072041d2002d00c68a44610170700405d02c0c0302d06404800022040d90092020444a40324078196500060855140c0c20320000903003480784409500b240800c03040300010780c0302d50301400044014101030800700c0c140890742e0040345251880041840c0300d009004000b804680c000c8095866100461008110b410800040700803440b0080d02d182d8400e1007401d0b0320315018035050141c0756008a1400c0d03020f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 813694064 1250 813692814 813692837
    0x90c1e050304260d05060a0905070507080f04050901061805010206011206020729040c0501080118020a020109150e3a0c020415050f04060f0614071b1a0703 68
    0x481102d1505100c2510100f02000b818159200354000e0121904400000607142c10580108208010b007603104d0307401241407808220740180c10609542d4400c2d04007040c1b5540390700125910b05540b196402141e400002d4000100e2003d6224210001008102203070300107490b1107800590707803101d0910030140c1248500b4030031400207083d6009000b8040c0b04d4030b058290851014941000072000c0402865030001c0c1804101c03d0246503004180144420b0034061503a5040c2005103407140d040c405841140c3d43c0008082ca4818400d40c8a0200345802c000d0030340c2000c03200e031141c1001e0161544030241034410101d0f6100c082d1121074055801040701000f0170000390448560101c04411210544c0070700c03201c6441d40c0050389a0340110305020442c200c450045c40e08080402c2903614283c210b10340120f1800b20305002036203101c1c62a00030f50700309082c01d60003c10805010f040ca8450b14074001c20741d88882007010308491040c100e0760165040010394800040585001c00860b001d0360f840640003901e018983c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 813695314 1250 813694064 813694073
    0x60901050f060f12010203130c06030c0e012006012c0606090d03020a0b040b04150e060114030a32031809060414040c1701090b150d0c090c1e050304 65
    0x3000c603020000d030010610b104d42d28542822600200c60224010b01002d00d40010054100c001001038140350400304903c0c40a035100030964001602464148801c13100341004551202064203040b083c4c20040301c11940e141c4000c1c11807800c0d1920042805842d203603032020b50070790703454001d4032440c00501618100864901041808040c0c900c05801b5401000d591b14085440081d03030b00d10480c00b0784000c110b141001d00c0c003104048490a980c40c0ba0914081c041c0a1030880400c00300e04680c0041e0112030b101a0101c002411b00725006001030844009902c81102c034041c40d41c0c208801c1d01c105400070340d151520b001b0b03980c4271f1050007912510490940c800303038000e103400003130590040342c040c00001d0340600c400310a010702803060714192055461a00208400040665030f890450b00d190020b2041010300c1e90340320b03060301000e4009e10380912824010007207500c6501d00100169000003640c22100ea40302600300040c12298108030000e08070300c84c4202090801d07400715059460343d0740d5040c41c555076600c2c3d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 813696564 1250 813695314 813695329
    0xf0506011a0712090f06030204050118060e0f03071d060418150216140c1003061d04021929071205070c0503010618050f0609010e04030c050d0c020102060901050f06 72
    0x14140d081c09080c10011540d840103240b58005043d40b80c0780160350762b09020014089803242000440b085851b40b8051110030333840700c3d40c40c0c0e8000f010b4441d0441144070310000f0b03080c14680c0d045815a40085000000703031401c02446d903800780340151410880712880b044070303140020107010040c0050703484a800b00d1640d85140d0040c1025806500101c008a0981e681c210f070144000d102594568860f2170260b50921700091303502941c98482c10100169031401c03200d04d00d88441440c0d41702081543d03800050941d126800c0140208181c0d00c43d0030303400c030f40307a01180ca1000b85c50000380300c00c3c1203404080b40514940e84110b4880c03540110070b2131043d200f40f1038100c84940c042c080c1285c1d90040003030001b41b140c400f40103900141000740a003412580c1d424030a001200d00007029200111054020f100c015100c403e50181560021406d0001d180d4403402d0540d1504a2108010904d120380030304221529800b40b0071091192003642039a000da150021102c0c2600da06846000d10340b42c2000100740d55142028 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 813697814 1250 813696564 813696593
    0x5090f0927010e060a06170606100f0504030b090a0b0a090209060411280f02030f1e0f040909060b030d021f09050106080d02121204060213050303070f0506011a07 71
    0x461076141100d05142031504c15a8040d8643d91201018005154070b2988082d025003103400810041c0f61003000034818400000c00201440440403040040360301c60b500725070140d50403190000341c60402e0203290340d03603442c044d10a171215000d074004520219043d000d9011901c2c0c000300700202680340d00b0104002040072030700d24184408200724a9180c9515020203800e5074103854820200d440d070f401c0010b0918448903e6070070441d00f082224090354000c810036541d4200100328154080789038880c010061740715403806810031000c0410300041c00ca560b9041042c02e40e1152600741711000d405410700d651009000220400f40c4c210500010b41d00c201c0101003040c00100010119500000e9210503084030344e0754120000ba03400c034480760b180d0f8640401200c82003104250795a8a010550b8000307801000016100900e42d5070001058441c4000b010b020002620f0010180c0c0e5548606243c44400000820382c1101e090054000000f0180c0d46031074032000da80d4000c00346034034081042d030744d503081d060001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 813699064 1250 813697814 813697891
    0x6010608070c0b070c0519061a01120b21011a1e01030f02090409030e030f070b0a03020918090309181b0f0c010e031201080105010f12050a02030d05090f09 68
    0x6001c6100850700401103840070300744040c47c09100303810030304003007050b900a40e08681104403a441c4141080e6403000382080040003000c40001c40b8014200040c001d4552002c100008008007040c01072141c40640c802c040c1e80240380700100180c0700310018031404040d0b0302c1d100120750030030045184640d4026000459601224000103281079940800502201c040303600175000a00b007400700720400c2c1420010082508e000310000c128141c039000c0000038600c0b4940070142095004550002c10303840d0706045101d041a40d030100e2185140983c02e2650303035005014018480d841204d030400440a0b030390f000c1c500901c507680b542040121101c4161255520100304104d40940030030070800c3c8528288681c800e492011b20185988414228032108480030680040c54103034501401003200c01340701c00e0baaa0844400542410441c4c9850030401d00300010410042d40601503048802c0d00e40c3d61008c000c05400004903070b5480803c034120f040c440d080b5012108144800113003044040c41104100e5009403d0410 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 813700314 1250 813699064 813699077
    0x323310605040636030c0b0313240912081005091b0d060801020a2a0b0a20130f050d06180501021204020f0d03020606190b040f0806010608070c0b07 65
    0x5204260900c004002004c0c5800d2119074814020401d000344c0c110001d050803d51942141080103a0700c44d001e4070744200030705002001e4007241424549420b05e000402e6811000c100766850703400c10030390b548140824000002d03400c50024090241d000c81da0004d0740c0007e00300c403460741d440204030050703141a80221001623000b070021b56081c2101340603a1015010f00c0001503110a0b421001400c80982e081e5403440c1d030f42c41c3c10321401e165044200e044086d25040f43e200c0c40d4039101c0c6c0170300d400242080300c6861248a20780305500f0b44a68100001c141041c04980c81d1060706556402d4101308504074000c25902ca10034a03440c2c0e02154654104140780101040040000d103042d64a0703908990101e680ea60810070740c201040f0035403404401c001d0200000b03955400c1e106409035402034460100400d61807044402c000705400540f806000301c006400d148480ca540c41d0340701c00f5080030b030024620800c560b03131041c0000481d40b18810341c0402e02905a9484048006800740d03034009618034020400e0081166 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 813701564 1250 813700314 813700367
    0x6020a1a0907051f02070518070e0409140706110114010b07061107030e1e06091905220509010b030a030e01020102160b0a050c03090a03233106050406 66
    0x4071101d0040a40134903440000750078240c002c1c00f074204006644814803030008401c6050510078502100ca522400e980b805c816001c4101e40091b005000c25500a4090a08807ca07080e19840008807801503c020b5103584400d1603051040c2400d13071f50444800c0e4011441e640041020401e260040c0c0380c2140709182c0415402c80c083c0101c11250000002540000c192000b41ea0242c10440781408002010981000c80003903c0000308085d0700c5011f140501428545202240380d00d03500c02ca8070064080182a1052450444034002505005410303d11100c0d28200110708004014070903070000c0c243c050080c101410564a042e40d1480e1400c0445065540070004901610390312030a1582c0203100308901001414581030301411600d00501701c0784106420030a114010308001135800c4901d5141c9030be901c40041b100e540305600c0d00481d000d084110400302c0c1c040001e0805002c0c0707a1045001c9410f298001c51610898a1b400004c2d115050210b0303410002482030b00c1c030555030f4402d1920520350142c400712 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 813702814 1250 813701564 813701569
    0x210b010b0309030a180806190c02010605180a0603050709140a0506010903120507050102040603020c1504230c030712031e0c02040c03020c1c030606050301050a051c080a05030f0106020a1a090705 85
    0x881e0074088d0011850b20000100c1c41a2050b00100075051000304841c03400d14001c0b0303040000c01d90904011302c80c0480050f10960403070f00500b015641c0301099a201e213560341e203184090905410f8440b28481c1d10300c000341030846d0601c0740c2407040030160750700603686103152103406d0384198003200d0404111042000b01d0128000b4001040201101d0381e00580d980304108800e810714203e001da01c1c0b01b400c0c1035424080403c5580301058910000200d02c508010030660b1814588011300340340a803d40200d08002400d807003801ca01a090714040e449500d40040803a05180165071600110b40214944c0f800d2440541040d600030148070b192420014035103041416a2417034031007110607500340c0725149019581841d80c0341c06080c008180c03e0800394103650400f00040c1070300c00f1034015580108000c01c1c030000f85040310002c04c84c2c290780140030745c1e030342c3c151a103001411540201c6402920030544000028030a02c00550b901080da084a041044103a030549001130004001e850307102c1c0d5100e0143c020401c0da = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 813704064 1250 813702814 813702823
    0x5010503180f06010f0e07140f070219050906060a0f08040c120c0603110f27090106181d04060c0201150b0c0d0c020a03060b0a210b010b0309030a1808 66
    0xb6804010400d075850b03c004000f4413a1160018400030800d00c0c01e1080594102030380020003517401c285203449061190201d01540100c000296002c0184c3d51038441010801ca18031051742e90548071810217944040038040c052283d0100c1e900000d030640a5410b5491180000c160814032494112651a40e500c0007200c004502041c265010340074040f0401c042500b51060140440303a000a040c00d02444000382940c0380103503d2904a44807000c1c60241803201d048040544d6000b004202c0380d05075840700300041074021000c070030014050018802042d4002424a80c0d81401850150004141e990303a03951005400b0007042c0805541d2180d04c11940f0340e00c84100f0740041d01102c0203554540c050001524a131419003080c000601203200010300c05600c4000c0c01c10241c0e0341102000c101d405411020410482095001c442e801c0840c071107a804816840b10030311503c60250740b04242690700e03507030f910941e1711040d16020407590041120703a681c1ca001c2c240d03058603042e4240c8540b04003507842a095041c03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 813705314 1250 813704064 813704083
    0x6020f0309010c090807050d0507081207060e070b0a0e13020c01090218071403090f0d0903050105240f010e1c02120607020d2d0201020d0c17010501050318 68
    0x2224804420442000d8007440340d11640750481c40c0680f40c030340c5401159a2503151a0159500a08841500c24240082048000c0080010100711020b200000c0d00000007500703d0581103413402e003040d140011880b0006092010765003907911035854450920001d40d030403412084419040301d40c0740b107010134003081071000d894420f0039800046007100d0b65204010007141242d076411f121002000510080c240d01103a2960b03080c40c080c104503540c5d00c42250880c03414601c0c030400f030a507104d8110b025800b00e40c01000f00d070440307128000900035a103850307401c100301030100d56040783d224050407001816131415001c5511800d4042c10141c0c88485d101000c1030040000ca01050703c620490b40c8a6021820011001008110600e020f0500741c1010340000391110150491342042092106258403004810811030b00c020046000207244d0201c1030101901039000062030340c00003480c24210709512400b85503c00c80c00e200b41000010140e09040c0150740a40003c4c2c01030f03101c0310f22050003c06005042058440 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 813706564 1250 813705314 813705337
    0x180601080102091903080406030b1801060e1806011d040603020607061d0d080621190615050a0b030a090c0807260a02040c0e0613093804090602 63
    0x81e1000f0300c03024071401e503d8001a02c1400d0412130790802c003290a03581964140c0341c0a00e0007050002101c400921010783c4030041440007040c841c0001400c50308110303802c401410545215040e480c4603052600c80517400c83e1910f000c65101b05a44000e0b81d489428071141b01d800500000300786890f50041101074001c0c14044882560b0754141301c4414140324020800c07444550000d10762704041c1c600042580c0e0018145500464100c0286103082007440b80c00c84035803040034103c9099040a041289600348034020903030f40385161a030410b0440c280b4002910668002410f134861051610864100c95440213065000c12030340c50f400d10000800d000b03507010081c29164001c01d0968144038551542c69182301d095406540100300340488580d0100c0c110340010f4044400103110344001d601a140044049032071036010900207042001c080031030703003c80c081c0c9903152001c001a1041409500c201100340311007600400d141031000328444001c540343c08560002400c0031403400726698828069822036040d100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 813707814 1250 813706564 813706567
    0x3040b0c07080313230402070f030306140d08070816080703020709051023030f100b0906010c15020d11031f03170a03090506040b0108061b0909180601080102 69
    0x2a000007008100c1c00362028501461402408840307902c0c80300c0d0184240500140841c40610440e40300307002e05401175902070000d541c3c4e0880c0b4a000000c0301d108040480100c1d00e000008200c15541f00040140002c01824924100103142c40d0b828081c0c0004038200d895050400050302001d48a400300300034036103c3c0030103c0d10785500e858081d0410030345800010007540340c8401c000c0401c254030000022105030b007610903a1510000d80e1a5004580900450f41511492190036030001c070000300c41c01880c10040d420044481d42c070007002000e082c1501e4907400240790450440200700350031549440020f059000600c2d113140041d18409880166101480502d404020042c00d0352528801520060701c000c0c0044142c1d0a5590f2809a802424062078011001107810103606001c1c2c0d000f58495074016045400350315003407030a048410000d00030314829024200200c1e1191801c1c030841d03005081c01d0344140b42070840410030320042c04401810030708020140101241242c000307118990182080c0400075 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 813709064 1250 813707814 813707827
    0x6020408010e2b0c03030b0d0b01060908011d15090a05100203070806030303091c170a02040501140307090e1312080f06010e03070e04060603120503041101050309151803040b 76
    0x24182c903800001800c045840850f201002030b501140d000300d910b505003000928500c40070040f0311803401d5850b004140000c513000204603d0b400c104024115510240240446590041641c400761504400030a10742d0211103204000c3c000c0707001507507008120004585a0a130301e91521842e101403111050030156001061207819648054200d40c030210a80055295041070490290750756420000a00d00d14100380035020a01d10030006090340c002242d81a092900b030a5000100030b41c01031180f2070100c0c0010524107000c4010a0640b481110380c6e032229408946028402d2000c40401405500f0110013850100c3c001002008808032203602a5a112064605642146254500600740354141300c0900c03a000e056540000d400c0083ea407044024421a49651520300003601c01d07500000c0841c900103030803507580b60388100507600c900d0140309415403900c0d10400641e442c0c03006507001c00c50798014404440e2070504d03e5074410b80141e240c0300d5800d5040500038815003540c116410071400d215001808 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 813710314 1250 813709064 813709093
    0x507031406150303030609180f070906060311040909030c0212060601090602030c1f110a0f020105100f05090714030709050f0301050c0a0f02030d02180112060e070c06020408010e 78
    0x80c660300441d0b41c000442400315440000750789003c01071149116410000008403890904120781e0b0b00d1a43c83d9080300d106124100030552030f9440e5026009034a450034000042a0303103e405104003a8903426a902e00d410f080c8040d00005c2d00c1100415414040e00594480045c0c94620030111042484000b03080360741000b000050032001158454021540248144807100700c010401920400744010314048a401c4e00d81840d025210303140f00c000b004840450301d018000c1d0085030f0341800c030b24154001c0200d1f40ea000840000c05201d409200346030b0b04000710034080c034200443c1e030680001640c05c0882d010038882580e0341c144c0d0b00450b000400074075043c004010f04d0919400d95055414210002c2c071280c5461403803601a0b00030380080d0b4040111122451480034000e20444121241104c01996500043e040003100307030006642050015259104089a84803603105403c15901402d0100b002030325500411904c5128111080e40d415600308000140c51009109001941404401808107003119051 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 813711564 1250 813710314 813710323
    0xb15070605070f201204060504080601170a0f060f050903090307120206071707140c010908010212010501050a050405090108071a0a0f142a07091503060b040905070314 73
    0x16818400e1050b02854110340245070300000c4030340130341e89003010001c11102c6807401100e100310810f2140000f40229486500c10010016240640100c0301640d0b23989982d1040c03d00c00c0c00c00200c0c10782010810300e00148008801c442114000c050100326100b80d210410700f1920262812143c540c400240482c01d400d0500c1002d0080c041164032501c0c078002600410070b14414100001c00010b5043d9429661b14000c1d020fa80c5140d030815190200e81c0c03401c4044550340d03c980412035001c540350110004502d5814001c80b03030003e4003100402c0d1640d18100056517035401c0000e003141806804c0c040840c441e00c54000580c005e04490004100140c80c00d1800141140b5000c1860b00346103003044060a5250444883c003030013103980c5011100300e01d0f041038008844c00f902e0700d00030b500c2c810030003000c03200e00d0800c030b45105440c10301080e80d035081d940b02080710441e10294401b10300a440208108040b55165200403460780014101161074000340c1d48140c05e120058008840c4e651408034141c1286a0421 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 813712814 1250 813711564 813711571
    0x51c0e0616031b0e0f03030f12010f1703071403041d010f14100e010201090b0f0f0a1514120102040605210c03150109260129060d0b15070605 62
    0x410080381034030500c43c0100b2101eaa0524203001d01c90400580341ca58408008a0b1200c250840302180c48016002c80d03c10306580a00c86c1114a100c24040401c11001c8c40000c00c90300b200500055148c41c80c907944100c4006c0d0fa00a5820490000740310002d192078031103410110f0692212010f1030740f0b6040002d00b0904100c641c2007034202c01d48102102080361200010f4000900c102c1c105140140c20b1540101d001d4070380395078001c00101080c010b120a0134907160410f80103902c640855691559559200c4c021681c105d44104074a005041c000c10116423a131007220b0062030081d010700007106100d811a404ea034031580c4083e00040f030000344503003110072a1825020090700181d9142d0340b42808009001c0e680000380c5501c07240141e08a071010168040c90761a4001d040c0c800800100c124882c500d4200d5400701c00c00100c8950806041112901500000128800701e15140540008030182800f405400c40170300b2240c03403a90740c1c3d40b40005540314441c2442825210102603580c0306189809001c0c4d52018 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 813714064 1250 813712814 813712841
    0x100303110c06040e0a15030b040b090607050a1d0307080c130b0303070201030b01050d1104050102240705070515130c290310050402070b04060b10051c0e061603 70
    0xa4080492942ca9104840c01c44110000865554884030400350051104049419604164100020401600748d9400e44654020310044420b681c1b6000c0c4c00b51102c81c100c0700940015810408082c1d40ca0080e04c80c0d1804089031000800d09020035004203141c000d1a410110003039004040001142c031b01800759005640d00034106000018101001c269640a4004020b0515860b184280441e92127501903c015521506003803004005004940d0407913840750203694014040e04071445000b03215010701c030f0a07203011001148040d5680c1e00c02142c2a4020320404c407040d0144803500c00500e04058501c2d070003580407070000461a8128a0010329113105644034003030b0140c4004410944260314168003501c0003112071301030b070b0340c0d90340b0740165031807207202c3c1c120796031007031001c0303488402e00c41c0589903035100c0c03803269400f040002c94800802100c1ca01d0703440c034040014000c100140c1c003980d40440302580d0003100300f40814134880b0502041c4c1095411034030074921900c3c00c400f6403591030345402100c0f04940e55 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 813715314 1250 813714064 813714073
    0x6060303120a11090612090c04090203100c140a0f020d0f080a0f0f020408070f05032d0109060c26070e0105091924030513110a0e10030311 61
    0x1880007510030044000c000b403070030960795841494a90101000c031420300c0002083d490b50745261100031a203410782990b0303a1000744981828180741e42450301c15110300c07940040c0208145201d002c0b004000c0e081440707818040020b8158500e11106000000e400c4518076074641c03200340d0744110002480d05101031031038800c21a4411001440300c0e00303e0103031504198810070100d4050b4640c00c91202a042545041c6480c9100003000a5502c0c0e0200d01c1c4d40681d40c802c6403034140c03250744000b003568500080710b105485613059440c010502440803030008442901000100d0070310496118401218400f070038082c0858251000b00c40442c40400802c500c6040c103d804104a0070400300003000203c1e040b601702e043c08000201c104040d5216400020311101d08c0000c11509034480b504501c04408071f00d981c2105000540c0030800140c004e000c0c0600c24002854070100ca81015101d03c843d030880c070708185412000e0448041403101c1090040383c4120820903070014228a18900200340542d03116100d18039400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 813716564 1250 813715314 813715327
    0xb04050c0d031205041704080c0f030c010806060d0e031602010f1107050607060204210c060905010203160807020d230a170304030203220302041113030b0c0c0a05010b0306060303 78
    0x704201c0024080c080f2000c0000d44e540ca620b01060354070300350115008440e8010400040c0c10701c0c0040c0b203111a000588100040e4180f4500303141d52030340c00c2405940480c0c6204c000800a0a124014098141000f2400704d040303180090007030700b523a200000a08144000000100955800c400e184026450034504141113841300503520b6250b170380a0080d035110b800005855410311000e901a28080e003d03856160100020021000090101c01942120b0301140c002002502c40e00454066003202c0f0182c014603d000740828412010079036171a401c8806c80380070302081c030145e141c00350600c40725440744101d03004c46140030080c01c00914208240003120ba1240940400280701c038140328030b1140215404503185c3d2039038641642140600003503c5210b2040394542c0c02145050700c000001c503030096400700107841054141c209140b143c1d084200381032050150030000200c0d0b1121090740100700560403410401c04d000d541b400c0104546094640380e44840308284545420700a6a410a1048004618000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 813717814 1250 813716564 813716567
    0x260a17070f03050306090c0c06071b14060103050c0604030c050910080105070c020901080a150213031e0b01151e11010603150609020306031b0118060f03110c03090d080f03040b04050c0d03 82
    0x90041c9032b0340800000361681c42c0421204103040480b42d034002c401150b45070b000b4582541d01d034000d1109071180d2003540b4161840c2e003000e80403642901e400104400e5058140710038070040540103444800705000d0b038403000480701d40a2144601170070442d81c440d040c1000c40d00410500e00341c180c002c00d886070448056200050300c560829090300401d8480546c4840c1003480c2101c00c1c403c2a84007030b12a041d803144502c20820402c5035545c42c5445100248241d9882d04a008100100100c0c44404107040c0e400510929606141c020118892840c0050501701c440c030882e425200a6842214a00c200752410104141d02e400707000058180303420b04600350303d0044006680c581021130004400701404441e001a640b240400d1055060a02006015180d41d0400180a074800c3c00000000907c0e104000c62419450001c80c0c4419410500450624003010104041c3c00c3d9a14002c6810500c01c0156141825000c0051803140740100e50400451410303090080c1420450200d9a105d0000000000c0009 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 813719064 1250 813717814 813717823
    0x23010b0d0605150306010e0a050f0708040f0f06020f070c0923090c030105240f010915050d051513110f07081e04260a17070f03050306090c0c 62
    0x32030304580003040b20384410440c0c408803040c403510701d60103009482c0085110102d0600090060001c41400c001550f50729900441c060800c1c0d03000700000e41000041400300e4480030200d860f45000761b019020f401d0860780c6800c105d900c0529076001880c8041480000d001c00c101e48000107040e80c0c24140258036200f075000341d0051680c429a1100f005540101d442e8980030040c000d10044c000d4001c00c928240310384104010204140c2d0880e02c503460400314030480c24a000045079810068403150b0005041c010100d2940700814009002c22406109142850703d0030701916000b20300c1240440740e40801442844040c0c144c14481e0710095042140e8034003502c403c2022500400121450180c80382114038001c0d020b031244414030034078a03008900d40e190412003440100221900504004490346a00400162070518070701c0424490f0480307480c03c07000c02d4000c1141028004000000341c909121551101c2000918481c20b4000034004020000141003042c3c416400a982a8105040c1451600346980d00e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 813720314 1250 813719064 813719089
    0x10809070e180604050115090905060a020c030c01060f090c0206010812090109080a1110030b0108041b0b03071206060327150e1b0f060714030d050423010b 68
    0x40e207128400240d044016a803852080c0d401d140607201039003081e007405806010304806070301070750013484000550017980c0c0c4140601e8603480001750400f0f0782d56001c004025080007501c007031240002c00454081c80300c2841003e001c2c101804c0e140020904151010044407806482c0205640c019001400800d07400110082d03050521541155100c829800403a90400d80d680b1105440c415005281c0c10010178039100040d19006544a502490318040c049094031049012240884c0707400001c01c003c90340200308010451091060024900e03960102c0000d03907882110b03e58005030f00307482c044050758042c1c022900240714924061007921820320481c01d01248140400c101c85c1c0c01e08041c8010401a1a80c052104c00250f50800c03250b250b03c40d04585680c20345401810034040128010101e181511b540007035014058070f080e0500c40581d85409042c40c05004a51b084e02c424031011090b031800c0d0144500c114172458004179400c84150106ea030300640c605800b82c0d9a41001c0c0c4c500d500307454070a0a40301 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 813721564 1250 813720314 813720329
    0x90f1701142208041502031c0c0e06070809180a0e0d0503010e1b030a060503061b2a0607031a150d0b060403080703270503150604140403030c020c01080907 68
    0xb102c45031440c0c035481c1440341d940500c12100024000c00700d40b0350040098017403074920b49020844008031140043c03c94a0040c0b03841c0129031200507030010350901d500030f031550360311400d4090724020607130001a411840541340c0d00b82ca016020100422102c550103403240c0d08801c50300901081c0341d0310074060030030b00050040c030349040c0703150300060024040140c4180c0d40320800c2164640d82d0500c03050010182c035581c040c280c045d118040204407045910401d150040f54403601e240d040500744c04010780c0000c08141c2c0b01c07a038480b182050500001080c0040c2c2d02802d02070b140013880ca1402c0c401d94550b100c8901076103215010b14820346c41c4100c03102040b03c0d125215103400040100310140000d540340501e41018007240c40100d200010190003034901c0035265549504e002c40941801980503012803240221a007542006400b290b0141c4440102604413000510104844045810f01c3c540e84030115002c0c0c00094440400000d065010300c1680b82a030800e280580e024580205001c0e580c1d95079108400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 813722814 1250 813721564 813721621
    0x305030f09011b050c0301060b0c120702033a020109030c02060c0708151b130509060f040f06060f05070f020d03020a0b01030b01060e0d0b060907090f170114 69
    0x101d41e21424403440c0e115a0b2040c05002c00542d03082c02d55550004c02c03590340c040e41c039024021a01007405000e43c1c00145d41c2400416110101080d0f500b50350304002e000b284c1502c40c010368540d10074451400800000c0140b2025155610888400c05a200a240568007903900d800159030120f5449030191448a8041e00e240d80d0700e0310402d00c45480c4c440346070f20500c403078086d8100d403400319030206160310b000c0d000c40d44c100081c0300203040c01c08000c5c0c490186c0c1648041c113001d4082140d030800e01d41c401c0c0c0c04400104080c0819584c5004603082d41ca12118480010360348040c280551038000020f00d60307080c42c1c5d143c90b6040071040c0c0c1d5200c601d6412104041e11640544030700d07104244c805c010b400181c0c5c3e8040c0c4120316559403454045a250300a0080b04041071501d24040c00d035043c05090024150340180e070143e2140c03194418409590380c058050b10400209032404600603600000c040010400d40700403968249581341560708480014140c01403c2c51404148000d00d0101c2c0314542c0030b88035588801 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 813724064 1250 813722814 813722827
    0x307020118090905030712260a060b181905150f07050102120f07050304150c200a061404020d12020c03010501060309050c040c0504060f032912070305030f 68
    0x141c95154141d1120003901d040c10920020424003001402d2160f204001c81c8034072018a04040c0c80c40384a03180745801c2c1d200380f0f0131400712120030741002641000180b100000e0040d100c0490391007a40c082024001070345000754100301d00b803c00303c42d0750154203000c41a140055045c02d00080184801c0303d82c80b02a4803005c6901c081da41d50800c100c6022aa2040003113642e0ba0914040c482c9564040f1201d1000d00002c10015840d5400344084910a03a4040c00800703e0b010548100802400040b201c40e081204003480350441c0c0803042c04898500c032802c0010140503809252002c2550080300380350b100c80181c2810301c0010f0325501001b0611603030014104405c1504210103c1c03a11945c0c690181d85582410300005035103406500003e06030340104140d803802c4001a00f40802d48055a0315079002441c200410016a846125103240020301442d01207850340031080c640302d6a104403403220b030031400c41222028a0740b8150440c940b03c20881c01c098000700b03240d40c4400d80c40340900e171050f00e274100c40012034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 813725314 1250 813724064 813724097
    0x30b0a1b050c10020403060917120c160209010f140105190302160807060c0f0c05071509181401080703080708070f02031b0301230105060a0926011b0203070201 70
    0x200e001e88034100f081107489954070b0070620f000d080034810540c0d000d01ca085084240081c00f00c1141d1419070b1006030400f044c1c5808004510070741c00300707469030325050103100c0b20001039560650136070003000c444801540180c00c001414800150344840d081c18445c1c10400010402d000e036000c80d80d00341d00ca050043e101c4450081040c03440b2040c1c0c8008102000004480041000ea81d20419179205699280000301c1c0d9075030000e4440c40344401016110343e0040c0303005c0002740340a540000c6109000c3c9040c4a07000c1d81c45071210368490940d0030070740641c1d41b521141c500a0750300280007401400480000c000440c999100d9000c0c901c5100009403201900041c90014440380f40020318403d90b0180c1110600300445040c8403440c072108a595201c1d50030074032140383d2041907003104213181c0540c0c01071418070703441c0c0360404c00f41c0ea000c201c03500207100b0a641c0005060200d10143c00c0410400581c2c0b804000d510006242194000c04c50003100d03143c60903005205a40c00801e032400a507080c01c1c291f1401d15144c64 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 813726564 1250 813725314 813725323
    0x3170901020408060a0207060b0414040f050f0d2c010c060b210c0f041505091308070308041502030c090105280903111f050a2601030b0a1b050c 63
    0x48000384c4a00014801d46003c981c2c0140360490003401d08100e103044410400041d240c4c1034030800803540324440400c010503001d92100308040d1107007048401907a2107400c0300f0b0500e40500d422038081aa085180c1c00442840e000010f000905c14820003103100d500f40010301031180c03d03a40070300802c1c1c0d102c08141454803160551184549040000c44490030052002940e17503a1040034075001c1c015084d810080c5080c14021404568040018151454104014003140c0d2130014028200c0200c038261500100d00c0c100020081e00f8040d550b200c40c1032501d03040000f0500e56002503c01041d104204200980000c60180e948000007460100d948010411102507008000c0301c0014a038180741c0745001d541d07900500c60740308a03031141030f101240c1904001005600010708041d0100c0d003050006103407540d80b08000410920b081800c02070310206140001d881c40c41c41444100008000305d40062091001705184683c1c0b00e201000c0034040e614050040c202c0400400b0000000e00202007000c1c1d00c488810310 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 813727814 1250 813726564 813726569
    0x1150503120a180312030c0e0a150c0c0b070201020f030a1b021f03060906090605130c0512072309030a11040f0e0606010f0f02030703050f0f0d0e0c0409031709010204 73
    0x1014a4043c0303072641411890a8100b07802200824642606003c10394040e02028025404c001c016942d05403402092205100d40a00e04070108585030b1010000580c1040310b04000e8100091260740f604054800a80b0381085441e0000041d8030034040c51840c07640c404140b1448600301600243c481d0a148040b91484080c107160603002ca103030005400e02d9951561010003100c0191070248950b0713548000740021903540340110382d003003c0c58a500d60703a100e109400603070042c01580f406514100f180b80c0103a950f04025a140000a00005c44201e1540480100700c842c4000c0c05500607d040405d60010740d854034a110300404148141d400f282030703681c0310b51020003425200388007884580c042c125841d448410460342da07804211211580640c15200d40c004045000d2260020f510349181c60710240e0b41c58010003400440e116040003010f00e60140c15000d0045040c1200c4080303000025040c03c0d0b41450010019140207514054504002c29441410705504080300b00104246440380c107001c0340a0301c04ea4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 813729064 1250 813727814 813727847
    0x1060e011406072915060703140313050a0501060602010b0427140d0201061e03080a0e0a03020d06050a06051005070803220f0c0608012409030c06050c01150503120a 72
    0x10300c2550b406241e00414103109001d41c1d0340c000d090401d41710804c615030044100140001c0c0090a00702e501c804c00d0001540c100381c500690400e0550250740e01c510740034448004440c036075101d030802c01c652030302401030300c090074421101401120300f4850340300d05402100d900001c13107402890306407043c000724480c9580c0d28188801510220030b5041d501038080c004503c20400c46c4205084076981005801040380c05490b44007015034a03105150344100c0d510a5003140c0c16030b20403290540000140e441350184c80c0540d105610200d06464a40d0600003220f10b26800940941c80c0405001c4040351b0040880d28010350004410781c90382c60704c0300d401c0f4050b0f83e4038401300d030b60480c100135078801e21100b050030510700c5118500040056071560401c4a1000c002c0c4210b42d442e1509040001001c0c0d41112003100030200d9142084400e5640c0c3c40d007043d80b60180d80280003180000815024a00c030078010518105a2440344a8a992900740866640c0c0d00c1d68038400304e00c00d804038800151500c142051901c2d007880b07 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 813730314 1250 813729064 813729113
    0xc080a031a06041508090d020c091008010213180603020603130f021005041a1612050c100e2107020103051e011401030b09041101030c0201110708070501060e01140607 73
    0xc074403142e50341000c813500f03075800b280c42000051220480050007442d42213480d07000d00541400d10301441500c000203400b002d09111071500200305a0400d202500b5070341184000401080d02e054104254031000e400f4241036a4104001800562948401c0b03d400c15042e5070050300750101414101030720f003150071000354400750f41c402418203180d01101410550b11000028601586940c500311038521900400b0754109440390b40301004aa518441c0c0030078407031a420030500e0300c00a01440c50134a01951140d91101c0d5846490700004c2e4410090314181030000e41400394003680c08903024119024180e40241015140c0c000155210200c9800d01000121000d0040c4596181c032480b0300c540d07007026545400246480c1100c0658500980c80300c2c019034001005400503020311004601500303908800030155900d40c1060220a21460003d000d40d43c0580303002921907400340740c0343d801d503181540300e1024020240d00501100c0c181d100081c190000c115501c0b6900c6210340381121704810020500c5c002d0050 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 813731564 1250 813730314 813730319
    0x101e030609080c07120519080903030a080106020618060105060d0b0d050307150207030e040b0f1009051302040609120f0804030b0414030f0a0302160f050a03030c0c080a031a0604 78
    0x3400985410794000095610aa483e0110f1105c4503410400c06006e9911203911b8001c0000300000058516006018a907d44410000843d19541c441c240140001d80c81200410219605002468001028991801c01c018409a40560703405043c0250751050344001040704070701c0c2030799100c0200c103007003e803075160400403504005440340c100c05070075203c0407a01c80b1000050303240342c422a002143d041c5c0f00d003031410085c032081c4402000821841c07030f001056442980007550360041001034030b610544d0b40405150411007808421100216080145801400103019240e006039200003076650000141121001c01d041c000003071a07010380050180000018080240801408180e2140380606050900c040d8607010303155070380c0b0500755443c2d003000e01408000c810511940081c151b424520042d03643c0e01125452303d421b50310604800f103031b160344941500d0f42055094080e00d441c1c10201d00f0000714901c202d44400d5407601c1503400000815940e220300d070045000b40da04c500b80094000c0c0a0030f44554 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 813732814 1250 813731564 813731573
    0x4905100e01180b030307020109150c0b01090c1d09040212070312032307020d031815090302061005013507020c0f1c02120a12050901090509101e030609 66
    0x1002e1001e0121400d0400c0742e2001542000011034900590696403180018906034002000e25408001041000070354001c0801260001c00c500d0b002e8190b4001c0003031003003001d1001401c1c903070384050002c00c0354004a901e012140d03140756003a40d00540507507402c0001318031b10015505152094100821030711200d1580e81070f01fa4581d011014848401100c4100c6002d4030142d011002000c490341d4005901141180b02c246200350005981540d2032100b210458941d951340c242d03800c5a10968003001035a90b50041c0c1450b904008141d0403049404101c4046810000001c2081070220440954411071320003907441c03140745450740e07888000701903203544080c188000c0094403403c0f880380040c13281211b03000001c5140750044c041c2200f405031440d102c01e00c100c0c0d5402d02c01c01285241860441d03001d03c1d021040858088242c1c000d2204840d0317140b658840030040050242ca590350051800350703a100c401c0006130030b407a040400c01e03a00a5400e880a030b401d400c0403120003900b1900020040e0381080150030401 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 813734064 1250 813732814 813732839
    0xb0402030312250c0b07120e0322050a420c0501060f0503030715090b010f090c08090d0c0507260706080408042106024905100e01 57
    0x6035410f000e07803d410f00c0300300c200715280c3c0c0d2401000ba15816a41c008140780a00400c062070782441402c0c0017041d46141e1001c801d0a5820040701202130640344814a03045401d86c3c00c0c0d00001d40300071540e114a40e4289050082c1c51551110032550010440344900c4400e440100c0428052600740080319004e04042c6000b17054416141b001c580355030810101054030480d103c0504142c8401400850801e8030a48540180303000c22071505400f1680d5900c0710000c200711801c0540a443d14000d0345212900e000d03d00030440304c5401d001c0c030802c01000180310320000c01240d040b100d4074603480c110090100c00d040803800e11352150b121045151070038560101e94491703400c0070707240744451200703079000c0d80d95608090700d1070301c41103038020042101044284103a200d080e8210b15040b00309440d564007000d0300d0303a6075012640300c0501a1701c105202c101e180409200581501c20400311034068008000b41c030004541c5030b27812440c02ca03005589600000b0460407149075030000a004654041905582d580038482d045c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 813735314 1250 813734064 813734101
    0xb01140703021b04180f081308030c1203101202040b04020426010c020d050d290f040b060d02090103021c0510060903030923030f0f0d03090803040b0402030312 70
    0x241c030f004400c4052180340a00c035120f2059940040103516044940c1c99540e40d52481c80220f42200703050100910070358070301501d140507168030307401141c0da014400c00d030b6450302c0c00f023008103d074841040003000400490318250034100c40d1240d41e0001c10b445d06100040191181c0d000d01a0407901c00b250015200c02a80c50902d50100684c0200c0090b6001c10482c40c00d07030300f81c1da582c500540e001148031480700d44107100500e411100203a0009000224020b14400690241c0380d600b0741001d0240380841c80e1812008448988204550400c9010780342400310300760707010b0380f94440d50003580440ca1a850340d020360100c03113691140d442100078448a85800070300074401a10034030142d072804100410050700400141059903010b48401440300e103000c850345205001c03c0301d0030524144403840300e08144c0b020418404508403980c080d1842e20003c105461034846a911400105800d204401340403d00317000440f038010380c00c60090350240e5100d00120f440c52042441003031400b840f181c1002010000201c00054 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 813736564 1250 813735314 813735343
    0x1f12050934080c0d0201050a05040905010605210906011403010e01090c0905011a070f060908070b01090b010f0512090c0a0e061305040b0a1a061201050a050109180b0114070302 77
    0x801c688901c64030f83c2e0743c1210501260000070450802d40558020320260030000c503d440c01501c0d203030312251007500341c800a0b4400030201c0d8004c2190041c0c41204010101001c0b02140384000b1031520055903a03a860041c03155280f6140e00f031201a0481d01d00f0740004c80c070140300000074028039100e441d0a0501c850240315540311249804004036402d803c0005803010017003020b0060b41002419102d5040001080307004840d42c5903503010b244002814040513100e01c501809902e035096251140100a0781c2c0c00c104103a0402c50700d190344c1304c1c00c290441c0540740300e6684200361602035603032030041038600901c2031071a41d4440c8280ca000104030901c019000e1003a40c044d9170540f1b050401e0343c030490a56100740c2c0c00600303800c0e6040000301005400e40c0031400e1907100081c9004540251000319940c0d50008981d10f101207903040c0140305908005805100824080c603128800314600050600e0380150004820404d5807541a0900395a12407050b030041403007000402507643c005031901075036520009180f4074 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 813737814 1250 813736564 813736663
    0x1111c0509120d1205150a03050c0108010509090304031506170d18030206090f010215161b0b0c030c1309020405090f0606041a0f0313021f120509 64
    0xb4418800482d005800b0100f40e1103050490700000d52003005032000a0420148011900c420801a61508000c0c070095000320044c1800749280c500050221a058211500031603c02047c0409c81c0070000c11501102d4020210031a056a0218a100500405d078010113881c0005e0060010a05011400b00804401a1a0302142c0500c4944004044065100c080d50144045c0481fa0f0141844030516102140500c1034621082d10340c0107568020100351941c80551031300140c59040d00750024489001c2c0701d00030039141c1c5017400550b81c0b02c601c2e910040203103800705004004201c481d03031000d050350308039154000402d0003181c5556684000350494410a441000a540480c0b00c08100503180c0f030190f80040c09591a040c24803003c495406299090041646420455100031201207001b441c0210000704011150380c15034010403e00c2c244281d0344203e1a0b02030f030442c4c440a50001c5200080070890100490182c0c0d4016030541403a4640c0403030300303180100400c0c1c980b26041c42803882070142d003090fa511 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 813739064 1250 813737814 813737839
    0x6090f061404090b0402070606270b030a020d0215030a0218011107090203060a0f0308090103051b04061b06140601020f070f090b041d03070312051501111c0509 70
    0x454001090760740d100034040c4200414070109000d03804c4a00d5015000e1320240ca42071242ea101d004980c4107520090004507452840d4050310016101d064503021109414010303000200d000a40307400c550131001b44911081294442151035000f00007401c020048003507034503403500b8088000039501c81e41c40484a515403070313543c58003913014000818911903030800170305c512400c000055000354000f82c211075000983d01070014090700d20840d80340146210710700712511403000300c0015060340c0010709500615035901401c2003041c2d009406071400c4400300c1c03426045620300310700409500d4070702420190020303080c42c0d0300207003c1c609520032078060300003a421a1007030034800800075201d124900030703181c2911003010100b0002061341c01800c2901001880003441c0f42440b0344013441c1404001d42001c890304007003106814075400c2544111040340180301807000e0301e0071920581501c40f03401049030500490711403000c1ca00c00108813807014a485085112618048403c0c040c1c59600100202481003000002c80c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 813740314 1250 813739064 813739067
    0x302010c031b0f03060923340318030c0c0f0501021e0c28050a140d0302101a031204030b070507050a0b0103061e1e0e1606090f06 57
    0xe601040048100040c0e0441800a003201e8841c07621000301c0030982c80c3e080108034503c0300c2c0303d00840510022510b81d441c5900e148942c0c05500000c0140e100c4826600741401c001148c4c1128044c2da80328800144000d0310941c205900400007410501100d06806410703208268008905040641c00b90840c0f03003026944e82542c0c64503100ca0b000d00e50060301b01d4103007800700061100150510000d80402e40354905c0c07040011606580707030321071005600001b25202c04c2c01d50f502d800a01003c1c000c2a2850001c9a00389401524407400e10701665004040c0100a2002c0c18401c2c0184510340c1c594020520241a80c42c40c1c0b203e001111135a06071003409410404030924104074226070031030740c1c4210f44282643c4d4000043d07800e27401140090320b05014140020300000c200d404414081c500c2401d0000340c07260101c030460302c0c124624040000c40762030854480f0084440d001144c4007581c1821700441c0703102004110f2428500c420f46c21401400c13500c03002088207a0003986050565810030680900b45a50301c00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 813741564 1250 813740314 813740321
    0x30d0504060e010e100e010e2d01060503031b10060f090e0f06011e030c06090e0a0e0715030e0102070c06020c0d0f03052b09060e0c030613060b090703090302010c03 72
    0x4ca45203c0e90294000c3e040c01a40b40d00605005001d00f0000904065040071560400e210348031410102c119610442c18400c01440040009025110081041904190200769a84100050020003200112401b100100100b024081c824400c82050000741c1e540c1e0f02101c44140c0034020200d54074142881d007402044002081e9000402020050066034a002c141524140c00401c041c1c103011442d20010000c1100c0d8070a88004000955900c400320b450210341110038a0080c003005c0303003107080c09105a042c40001903018103451001606410510341c42c1e100341c004207140d140c0c800b1a5400880c4c0a01840b501215a13403c8a05503020f07200c00800c0380003009a103907800c03003005044000d03c0100b1000b01e88920042e1004041503156000d880c0389908200420442d0161030451941d110104041002080c1c001c0500d8180c55070000c0500e10100000a6150400104078400640d10000f50a0a109145d008400d0314080079200c1d03000c078100403000601a0548100a60140d03090040d8259458172078072 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 813742814 1250 813741564 813741581
    0x825091701090308011211060c0a0201020712120f11120c070509061003020306060702120105060a06050f120912040f0911040608040b04020f040c2303131b08030d0504060e01 76
    0x1511031086a00b0541d081b28450850f40050b00c08400c600114040d40d2142d4004089000c142002001040c442d84002860100d032a00010500103443e0591b5000490490465242036900c1c01c20700511100705400b00c45240b880032020555100c2d41103e0440300b000c6200405c0846210016907400b80d4136141840421041604d0310b40d001700d21006002005c40c400d078080d5400c108020120342c54403019800007270540d410020ba8140c540d54400c1480380c40d01d440e8000324000c100d1070a1007800e1084040e021100b1303003e212242d42952502c440000c03508402070260442c5100410b0020342c031641c03281b080070142c1089005880401d460400b207409003407145800e54085481c00d940d00703500d5540d640d440b1000e83d50082c00480c1c01011018207840c0c150358600903001131130000d66605059100030b80074805080136080ba40c51050a00700180000002011030590b001034001075940440017003801c4c00101e084881d8000303882d9000100340400402d40c81d0b00840d000e5402401d080c42140076003141a402c9401c0340 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 813744064 1250 813742814 813742817
    0xf070e0919052203050705030f120105100f0219020a0504360c03080706020c07151d0306070e06130902090f0306070806120f190507080a0c030308250917010903 70
    0x4880701d500180c8150000e0078014030487c00d4908000613500701c4074454104c425000380a0440100602a03402c0c90000340d030b050401890400c0070003910380360180d01d4040544c0c03801e1041240882e007005544070420354000030203020f801000494850012410b401c103071010000c040d01030007550f09101070200b0000c40300c03c90300070310040003031072841d56614085e42c40340d84c0c01c845c1241c080c000704000300000c1c45030000a14041c9100c9400401840d4010901e11020002d1405100121101c0807207440c00104071f07502c03100500b4a8010509501c0002c0c0c0704d40102591840b0080c468000480e0030852500a4100d81800790750090307141840c0401c05440d010119480b000244110000960f00d2810300d511140030914081902e0403450224a002d0802c8422115143c5040e12002084104082041444000c081c030b60051b100110700c5a451003d414224071000c2d0401080c0f101240714201040f0080002510280441c030301d072041c1280c00751003a07000d8881c400d929040600d400060100601030840000d0b4103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 813745314 1250 813744064 813744121
    0xb01030b012102130306020c1b0a0e06060d1103090a17040b120c0f1602090a06030b0411010207050936030703110c09250203120f070e091905 62
    0xb01c1c0301d01c030029040005060a1500c1e01100000490500c1c0700401030304100303030041c3c15020090038040110300c0034a40c1a90054040e1541080504c400d542001c0e006241115443e55941c00388143c0070150580a0303550384148000424440003500010b000380c00641b10756074907151044081c081c164140100e00c1007100c0c03d1010404072020300c0c1610259940900034000d054140711040403a661160080180b4000d5016160080019803400c00b40c12940720002c60024480c0c03070b04655541c0d41c200000b40c4010040c40c5071010040441e0700900510016010243c200065440c201d245800c00d100f941c200800b102141c007500211580039000000d104045000c02586011280d039002c8440050180700c8141ea405420148200c41d621020440d00134082800c101c0781e9011804500c07200e1701940704a26003550300402180100d20030b122500c40e809000030300d0688450f82c8080040d11403407051440e0551000c0034034100f00a101441d0b03002030001480c1d6608004542d280c5c1e0542c201c40241480301c61601d0724 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 813746564 1250 813745314 813745367
    0x20c01020a0b06013c030506100c030503040602120a09020108070c020a0b1c180c0f0501020615060c010e160632040f03050309011b0209060f03070e0a0b01030b01 71
    0x70258051780400004640d00e414696440e01c100e14440b540c44d0201c07010a00c003105448603858003501c1c1d000341040b81c88100090039528041c1c810b40154000409200000c400982030081d580c2c19075001e000411110507241c0740c45d02c0290002d040c0d9900803070100b445680410f0141c0c3c8141c00380c00f80c156020300380300e000d00d0802c94480c0a80c0c0011a00181d00c0c1850416290503007a41c1c001d04401c000140350280120700240b41c6103000c62029008519540d2003010100001c0ea40043c10710b820107003c5c81307624050005000403031658816040310440070b41c00d0460311081c07142d00084600f070b15144084c1c0d00700c020391180c004540402807010789088940d05480c1c01070364010a142041d40c0700070091440c2d407070b0541e51524040344e407019500a990320f8101141d01440d65070040c00c0b150802000629008181403581d000400001018080a005040c1098140c9061314104010405000b40300345905e1a441c0500100b000b40c142240e085000030b00300b541300c003103a50145080b440056034040c0318590500c0b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 813747814 1250 813746564 813746567
    0x1060318021210060f15020303091513050d09090506030f120306190303050301050a0b0f0a03240b0403050715120911090c0307080c0f0a08040606031a07020c01020a0b0601 75
    0x3070012103107400d18003c000006080311120701c5210001c10114481034070252400405450105009038424295001003007000b0410101003000d12010b5000188a03504d6120716101000300e9840704401000c61040d41030214486412140c624201e82030001d06001d90303500c0000303250711400480403149282d8001c108511401c28074501440d4018005000000b0165880d0b80801c0c902c1c5a5070300030780c0030500020052006080a42042001d441402c01c110314140a40c00005442d200f800680d4003010341e6003001e101c43c2582017000c0028841c2408003480304035100c140005e55544540720840b401e03c03030a4000501c96074403240340d280c012400e440d010080500d0707010400c0940302050b0112510f0303200d00c0e003550841d92511011801000d00031000341d1a8508443e002d84410405400081c81e010140060b210300c041c09030460b61072145d0351920042d1a1128039103003000d04042d410091412a800d07400b90050a4400240c0d44500d00580c01c0302c0d99419100c0c01640c441c4921030001d80f00302e5000700022000d5 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 813749064 1250 813747814 813747829
    0x602030c031c090b07050711030607090e0a060e0a06050112111204050f03072009060306072109110a150806040c0e10050c0c1917210d050106031802 65
    0x190500540443ea001d055070301c00000f64801c0385d1440110741c021031440b0130b01c850b01480007107480b4103500516090401110280c503003042c81c880d043d000c2c6900c60006440c0c00f0315070000401402d171300c000508a4100409600c028141900446000031541c64442086001501918640c1144102814030b82030008000d4024100d0050041c1d0356031203111000510100100001d00c2c41c0c0d402585403910325030407000b10481c106110a038080c4140000001e0051642d40800d14541003541410000b44001c10004003c042c03207580b0207107003481860a81800c0174440040d011400c0003904449400c55030b503c1d018183c60040c07041d00c0750000a5942c0d4001410b6042ca070f8462408116141012180010f03084005a02280c8801c000c0002039004508020820b50400410800340802c07500703440031039241425050480100c3c800c0d8000440c01c2e030a28600344400b800b1031031101262868404410001070000d040e950302a4440c0a102840c14000042d4248070344111400c2860703000704900301424680801c0003d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 813750314 1250 813749064 813749107
    0x12060f0b090a030f0302011e0903020d030b0f0901170d1e0c0204240f0b0c03030604150b0f0304051605181902040e0a1b0c03141201060e0301060602030c03 68
    0xa40358070750103c00709031303042d1064220900c6980046a24a014000004280c075294030580e81c403070601c1c05c5000044c0c0c000c82c20401300380c0d29140008801080e40d00180d011403202480b16000000c07a030022508840255000345a80308010840e14000c10405049a400713500c0c15280784650130043c1c2c00c9080c05c0c4a8000034030034500007440842c0380c0070407440c00e020001c0305000980720803090341c0007040a26480000a001091070040131410309400041280d140d1100410aa1080b87c0d00c0c949403000d0320342c9140f150702400d1103004c420b49960001c1c00404255205075019107682c031a081e9a000000480201101956030162644500300183c04884d142100090a4619120080704442c0c18801881c40604000c0001071442203442c00d11450716411070700c1c20741080c00d903a001d40c4100030b00c1c02e4109a0181c02ca540c1441c1094140308407074842d41c014000c0d138491000c114481000000e119501886050784242d0480007004050390310002a69644103285802c11550002d2003901290121003602654 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 813751564 1250 813750314 813750319
    0x40b06011707030207060b06030c041e03081b1b131a03030a120b0f0a03080f1603030516020a02030d1d0303070b0f070504030b0105040506061603080712060f0b09 71
    0x502520484540c0700460446030300000a6000c500c5000f031111034000d08100d440107a030182d2640c14810f0211095200e18042e104480d001071200b4202e00f000d070390320b1000658004e180079486449440c00e052588418251020381e62084182e40e94a850340340e064103286410082c11011491121880b010203400161001c040d04005004011761941303040c00100034120941d5281003003075400f500e00008580c040c00b40e40e8000c2081c2c0880c05081e80301d401a1005503504490f0842d1941c05600341000c0b18869994088043c4148602c81810180c164000743d00400401941d407208020b4404201e0307859910800203581580300c0c054103c0140d00800044110001c0c040329021030900000100f0314561100710704a5940a8510422000d61619210745401c80218909245001c2c510340b1030403104941030190920032603803000894401d0340c50100311150000032400002c41c10840341000742100b1000c407a00340108100301501c4041800b14441e1f5010f403012219049101d0f4149070300303260030fa0087c849058 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 813752814 1250 813751564 813751577
    0x2a070603180b0708071205010e06190f1d01320109030f05060a0b09013605160801140303180a080a0b070e0a03110d060f02040e010e070e0306040b0601 66
    0x50100b070100c01c5862281420f5111010355050102d001008100580d5101c1c402503d0038006001c4540b8440c103082e041481255210018412070801d0200c420450f0b000003003c03a100031002803036206403401480700000c0c01f800c1600720307070360750240c1901c0c5109000a01801c40420060840c01c40c102d0074069000101807504540c083e449507109411940444d0054030b850340310200704800701102c0d00669001207000d50704924954501071920080e19114902e14a8502440751554081201904810364000c043e88051000d410032440001c600c111030380320780000586c03000c008200043d1440000402610107402546810104080e10004420325400903500c0f1103510400140450200102c00515018032924145404c0a12014100004809034903000d07507a617020820114087c12024601228103880d41c00030380e01c1f0307490030781e000300304c80b00c0081803440c4045000b05242070802d82d018140d5168118540381a21454815101c1d009400049545035000d2000a00043c06c0801c0c0350760080810706024 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 813754064 1250 813752814 813752861
    0x20f0a050d02240a02010e010b0406030b0403110c100309140102130302040207051504080406300e0a02040e01020a020c0a05092206020304030e0f15040b0708040302090702032a070603 80
    0x301d1055029030308044c0141e4640a01c440c00d91000c0c0301d5000e4121003240c0030441d241c0395607504507200c0d00051018003071100344003044034501024801d010030304900810302226504c1c1e80c6800781c0180b8a0210070307100d0090501c03c4034640141403003240c101480c010390b20368020b4995400c10000e5840644100c480e8081c81030000c40d06030500800c140154841c1101c3c03a140c9041c900002c00c100c94500c1403a2031810f03420100c0082050f0411010b21406684ac00494594648079a0929107400b00070001c1d0001d28240c00c0a4a015040d4064818580307030f0350917071700c4980e000700401c00851142c0c082c2c140c0c420320740408941507651100c0711151032400060008102c01894541d0030881c5c0080310158041070503218840f54900e03084c04526000c4201703c4404d04099140c21100a15000b030340243c5940c0c100000344001071201d0a01540d009640c0201102140c2c9071501000f5200d8000c1900741c070502070616406602c803c154003070150040c0003500145416890240100c0141100b98040d91106010007400d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 813755314 1250 813754064 813754129
    0x1a06130b0d1208010e0901060b0702130e2a01080c09060913061503050106050a02061b0f1305090711030d020f0c01140916120f06060e1003020f0a050d02 67
    0xb140c00c1c00c1d02622407040c1980740c2520090080300c000c0c0b0381c6441d42d2424100340080c1c1d580b8025030300c20580585041c0b0301807070001401401031010610151451045c3d01403100603040410451151038494200340d20b80106a05c015900144c1c2907420f4800c000043c0441d1299007840710141025500041c148090280019030f42012610079410005a05080c82d00c0544060b4041c01003500424103468a24545061110b000f9102e0901800c5030413122034000010140780c48140544070031a1843c800030380d072400244008003d0b049240320386809513030000c00094a00f07000c1c5403004074995481d0702952510101c080000000d40c0611180c9014020070b03c410011041d0034422010012050079145200d8100300d43c1e620300d808542c2c0c64040d000c41d00d841c010300601c003401c20302403c481c2e03208038460300c5000c5174a0708001070308481d04071095040c0c88204000070f09002641d00c3c42100c0c0266441e04400049900740412040b00e40038480d0080031074151040107040001c0c050380303100220400381c071304441201d14 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 813756564 1250 813755314 813755333
    0x50f0427140705060306091303090b1b1c0915140a050d060e150607060e06090d0905041a120109021009091802011707020102070f0b041a06130b0d 64
    0x3080d107040140403000301d19070303000300300510241008031042415450844001191024001c080f01004903031000342c035003014007032106030015055816580b6118103e444241d411504895a0381110384500c0c03055040b0320f144aa186020307280e056485d94001d9041c99901000401c03150150410045412491b41c0090000d030050128803070350f6511142e50744025428402a80d10b1900704d80c0c4102080c8052001e0359001c00d40252811005403541904c8d07880500382a00201134003900001c1c40d004c0c07101002905403000c0342c403408540f40b40d219103180341d0b107034800e00040350203100b030344900300b00d010380c0e21450f0385020b54441105840500021604468a80c04555041c480c001d1910204140c0c400a101d035a01900841e500051641242402004590002009802095101340c0602c5000c008078041c0e034401c2d0102d0707000c0f980014038188500f159151080c1c0d80c4000b15401e03507400e2580a00e807070384450703100c400318000e0070005c04001610b0040c0490000411141c070540758003400382d841a6000484000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 813757814 1250 813756564 813756641
    0x30103060501060806030615010323011d09060402090402211204090b03011a0d0305160f11030a0f0b0a1409030304020307240e0409050303090109110109050f04 70
    0x30004505949000c2020740440c402402d101e100f5002002007103150071482541c608201c0d0b0901c0d010800743c0c0d02039680340100280e01d4000c048151403600100320281210108541000d01c42c4540c030056480d0070f51203480f110140c0b002544102c245011038090302c0c2000070088800721401c1b08a041c601d24800082c54682e900d0b8142c814208046030411080030548580130340c20714194000d0118003017071520034410044d0240c015214400f000c0d01c8900f81441a030a4811002000020254010b02410071151002c1d59807811115010030140e100c04904000c07230202c40c0300c0d6110325400070540b4075175107210700403100a140071a0682e8400090660500500020303004a03e444059a5682028010306050450703580100e0310f10b10303203020800e00181202c0c000284030740c078610301420560f6654000601030140c005026010348404420300c0300d011410760108000b00d200e00191404070401600640e500c007894402c0be64400d101600114660415401c143e04807002c480342451442d0708203004003000c20084 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 813759064 1250 813757814 813757823
    0xb060d02030f06150702150a090b0a08043e0312070f021207030c06050715061806051c0f0602090307030506040b0916140a030b01060302460e06030103 66
    0x2c00520100c2d040000c0e02c44e40151695000380d1800c0c00da0b80102d503c0280f00103110115060000e03c17030302040d10900c1210098043c0c0d05280c0d5032170200d0f02004055070800d0714192082c0300c1107140d40e5070152200c04171412201c0b140d0900021211201d07486d18040030007891841d0075001d41010400c080403810300500d240ca00c1010b4a8561005500501c0311040d0505482201d86d4001201880810042d80d180c500b1101c1c14903015a44075400c1c86c00c00201c044040103d400241462408a640350490004603404103010030104581607036030040102d088000d00b000d009041c000741d90000810501e980400b8100e0003880b01510741184840868605940e640c42582c070358010a0038041000541c135141071700310040c50010480c40340e4521a0103440e00c00d511999a240da2500d9040007151503c035051310046410522204c0c80e580e458030094081d5000c0100c20081712007603503040082a2049000c0b0464124070a00041c0d01c03490031504400c40d821807100103050000d1003203107070102d039990343c02140a50710a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 813760314 1250 813759064 813759091
    0x60a180c0905120304030f05100203041109070309080d02161a01060f020c090c0d1b050918100e060a03120e010e0d1203022a0309030f0a0b0a0b060d0203 67
    0xa0311030003000c040e8690030032071240400c030f01d480415a81c00025241565000000c00502d80d5091a096242014403180040c44034004403c02040c0710950480030700e0140123a41e00840c641c1d40c40d10032030031a000054001c00c100400d002c0c130400c5a51641c0600b8802c148005031000d042c0e000c1c0c0740c440784141c80143c48402640e00e20010701040d9442041000300114a000030410300c00340e1000a0081e61005016003030901d03000c583c0c0c408185141e0008090008107902c3d091003641103200041c8142d111070780f001d0042c085d00d64032050551403c0e1609204410060840710b142e41000c12a10700d60102500e807540c000c080031004008101d070000105144107007a03e51104140d017100c009480805c280d100c3c144540291181ca60114869035442e1f43c42c4403003490010303030b59401c1021111410001c0c0c0c200241c1e0280f140400d25041a0004c010300d8040d03421070131500480910b40c05950342d01c2e00c40100a1915002c03c004c50441c118540000715031500042c45941007001c42c20008040f07820444180030300c100d8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 813761564 1250 813760314 813760331
    0xa02070308071b050909030702040b0f060d05060108060a030b16020c12012304080a0f12061805010801021e0a0521060f031b090604110c06010602012909060a18 70
    0x2020b0f034400c00188800e6640d03028138909041166104d0246102c064025a01c84144c07014a030307603180c00300303100d62002415984ca40214994400003003604507880c501160000010455030f1905280050440740d015400140c0340d0341e030b40603104e003141450b12031100790b208d0240f207141150790b180714071103034005843c1c00001e40601c01c200c08078014140743c03940010440060300b4840130070034500c102c80410b100d40c1005469902581803c9803020031502d0021a00b900d88080801c070361025402d80e0f07441007610382741804142d8940c03020500302e00ca03401c80d4100e100010703400d06052024010242182c80150705190741042e030345a02c040001c07240400e80a040031185000c004440c9801450107040c1070041d0300910404003196a100c0c00075800e000500d2190314000c00242a6035503d4000c0c00c06641561032254507080304101141d81c88074280504805542000303001c589a2074940c1c08406030003080607040120503c80740030720000794006006150031107544040499031051001541c0c1c018000e01c6000580c104 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 813762814 1250 813761564 813761603
    0x11090109291c0c121b12030c060b220b0f0406300b0c03072304050d0c0b070809030601081908030c1210060906090e011401270f0b07030c080a0207030807 67
    0x44082d001000c546c0c8580390100040303540b152655204684c8180300146002000001402d00c80e86a504049107100e80300c1c50005004064000c0c04c034025060b1030386001400341104100507160740b8080c01308040c281000c1c3e00c429111440d07003400b0a503207007683c150505507a6140e003102c0e89801c030ba0b81980c00c40000700303100d6140d611042c1000030000394844012003114480c0201c0d5603100b28070950b0321452401f951001801554146600181102c44003196102c00f6403030304076526002a418072340b00780110700001a05e0207012810480d02210140c1454003500c4039511800583c00240914404031818030590711400d000320075050141500e1001140d41601d003e40c0101020503c1d00843d0401524050410070320800020340b40c150b94810051488030000c2d00700498009a154110044520b803420320091207010b40d002c102c06584451080700a501e445000c406102d1040c0000100064001c4503000c0220350fa82c0b010b4040c5c540c1500c1641d03191903413901c4000c2290000340060740d449042c44005030000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 813764064 1250 813762814 813762863
    0x3080402010e0607260c061627031b091a04050c12040609050109080f0418020901020a0f050f0304060201020c060f0108120711090109291c0c12 63
    0x4000071183c1d149841a640d0307940713404c60030400c0d590300503a600b1181c0114241c201401d541d603c019900c1210064601b0005000c588a801150400454841c4c85429108072400707100f00c61010302c140116004a00c1d60b07071800c076000400742200c5006022050301180d41140b60140401c00c4150042c0080c00311411010007049a80142c00c1c011420b42c05c000030741800100104540d481a00800d0008504151b404c085001d0300b40c40c00003d000ca00d0024440301d010700078402034010340381500f10b000381580d203011000049201d4507103510701690000b01e00c4c100181200c25445034182c4620b081e0760352440803090340c1e85950000d40103140940d402045034445402d0811600e940706103112400700300e551401c100d440d210030b0001c03000f241400000490700203121544060307000c400400740c81c41216607518189800209145c81c20400c071510b000340002140020b10b081350007540401000b2044115207001e903980002025001101c06290440d00002d0100028031443c55190042c0200000d02d011544a01c00380f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 813765314 1250 813764064 813764087
    0x10506120c01140c030403080f04060e040c090e1503030309030d0e0703230f1006080c030601061407021f180b0c0303040305030c07141c050909040206160b040308040201 74
    0x4a5101401c03181e5140c0c0c0c020030b080001d00400101540d100c1c19141e8440c21481180c10142100b0b40000780740305940107510092040702c030f49070f50f074542c0c00c400c840402003550200c403020030010b1202e02083c041c01c0e40d480303841174001a0841141c818140840c1c0071a0943d0000c452034038035508003141e0741c0c4110b400ca01441b00006911800f80c4a47c90555403800124018041950a104001030021000c01c004002c200100c1d801c0d0000c40340c48040c000c000b0741c05031100d80504403c0c0e028402000c1500c0c140000c040341038581540b280d01c52095041c010201c95045100240c0e44908440e039035040e2204046078110b9611280c0d070340c804c0350000355492115080ca280c0e00c95103e000040000c004107410110039a5003159052401c15903d480348244640180245040075091030703c0110008940b0380002001d8241c0d404810301400d04016444c01520725010382d80e216074000c0c2480e80007030014035040300240310500d5041919000c0081944034050058404c4800728040781440003403006640e00840103503403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 813766564 1250 813765314 813765349
    0x903012412080316090305190627060c0228021207030f031b15090303050a0c02030409090201030915090308060927030c0d090f0b0f03130f0212010506 66
    0x10700715035945003445880010a80344c01480c11403d040c0d101485030039014000d64000e012150822a01800750034110090402121441d15110420b07090526100c500c03480900d003800448845141621000f014110007504c550460190032004402414015400d10b460740c008071412202c40b8840c414008050345e201822111a80196010000925900391000e50194903290010000e401c1c0c0b10708070100c8070404c8009140f81e03201ea8807101441c03a26485170080078002da809010540f5402c450104440000f0580c034016003080000b40845e40580e041601d00e50310625001520350001e444001207481c0800301103121545590880d01810350105880d03801030011501c1c9546412712000b1186070002c1011001d495000180a04054403414420390310105141d800741c0e1103850310b95000030310b066042c1c007800c40c85806030710b40400e0300401401503a04110b00501c1040ca1034650b2491801c00c0c00c60a1400c84544500340f200800689920415401c40078800001080d40c1c1012001c001680480e441d10740c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 813767814 1250 813766564 813766589
    0x506270708211303240f141501020c01080c0c0604032006101e08010e07050a0e0c0f0d0b1801230306150f0402030f060307170304091109030124 63
    0xe41900403080c4208403030340580015001801c80c0d1a540c08110581c0e119402d082c41c1c4584a0000c006c2604041460700d440d000c814521381d542181c0000810482042500590000344c100d0101d5014008480d0464000c00c0c109041c1030300914006d280c82401c8400f10001464040190000144001c0b0364000d811004040e100503c0d00300300003280d6414502c83d6520070b000080c0760344103030042603914002400300000244050403041c01000d0341d40740e6600c102402003542d03107000a549410005854041d20140601030703e443d406008190b41500100c1d00c03038401b01e5841300d01000541e59070a4850ba150700a04100c0380540c5400d40664950360520141c08440c54444580e40b820364004c1101c2c0c0c0e1184407040904194485680410140310340002c007a9005031000003440710019140c02c680380700d44005c034100e52165403503600c40d9605e040c18107000711080d4401e21003130011042079044901c1e5500b442100604108441002a094400201d0000b80d1100364206040541e41c0051128025101c00d40303008 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 813769064 1250 813767814 813767827
    0x6060e090c180702030a050a0512010f0f050904021e150301030c06080a0c020d0302030a14010b070c0501050705100c050d0c120e010605010c0b040c051525050627070821 74
    0x65186d1080c0324004c802c20100052202144e070041c0260ba08804c0348510a07000d82d03854004410348482e440c0655860b03000100000030320351a094080314451a4068509440c08480403404201c400a0704800303076110822003a240354201c0044061070085000b2034013900307131a10341000030b010f92601810072107165060904c2440c9241e00000c81c00000f0302c0c0c0e41380041e5641d50744904d000c0105143c0c0700d800f20088060000060340f980710406041802d01808140d005a035507140150b60b00e200341070f0028240e0308040342107550b41c04164011501e8000f00d0031300601e003034018007500085590060f010f0020442c04044a00e44c00100d11a800c2d401400c00020840c80e030825002a1100070b016030020030402520000904004090800d100103000203400e0225015492030320b000c140c1c005a0300035810341da80034140a0b43e0302c90341081e81c90301d0750044064052501e8500240048410140b9040421403004c0c6000150030002c2000340c1c010024100030304140303100b06015048015031050b03209100c0b001480031 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 813770314 1250 813769064 813769067
    0xe0d030806130608190c0506070320010207060203090d0215092d0a081909120807031e020d0206060613051e0319021809120706060e090c1807 62
    0x8a5800c888225003040705100000180006400329802869150040c990506003c1c1740c01e049180040348103542c50351980d6154010300001d80241c1c080038001480f5400c1c10a050940b0844082411509400244c90488180c880b601664002d460341a032680c40075251183e05607040c01116814002d081511500303041001d09140c0d140320300150f10580c009100c120421006810501101d000b0400301511f540c0b2106d82007040941d044403490781c01c2402402a2107050074400c14141007610b2481c9802d04110441d0b441e1032145410a00040701031041808460005504c0d840c1c011006602c907900030300034001740c500001d05082028101501445091102c180144950180c0a00356841506c00c0f542d0380c0302a01c11910a509208030b01601802151000507540c0100406035002500a079030070f070380c50b003080c04d06100800c0080320f07550174540020b0305001d04000800d00420501740100c8010801c0c6844154080c0940016035605940b54840901c02e4802c1c20220340ba81c026466a1107441480d107440b140 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 813771564 1250 813770314 813770327
    0x170307330c0f05160c062105220203031303061508150a0b03070905070306170f06010902130f0f030b07051204020112140f0105010311180607060b030a0b070e0d03 71
    0x800c018088082852040400560010780c00c139504040216401030707507542c014019411081c05a10a4000b0700104980c541c030381d0003000c0c01120320314150200c42d0313000c80c4000707543e0900c2c020032039043c0000c029480558100c05990805140130307540c001484c4141141d0640141c065902520158004214114408000300c02d4990b000c040e1960100c0c0c019241e00000341841282d401c100d540c00d207010207201203298198401d0341514a00b10340c016580c4038030311510307070b98000058115990740e00c941d0041c881d0040a8015114101c204035582519a40329a400e00c0406081c1e00517440100044600700207100801c000c087c0c0100c800e040caa4036040d05115000007268004002a0502c01c078591003000c94030565114001c800310806034040c1904002c00109a404820320030b0500103824542c202c401640e030f9201b01c4017400244602200790301040d00030301089800c040d80958400b0380d50800c1c0c0352161018800030820030b00c242c1202d811441c1131503001c0e044024000301c1c0c0d4054820400078200182c3c1144d03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 813772814 1250 813771564 813771587
    0xf030711011a0d0605070c20040b09010b1c060807060305040501050714180102030d0921020d0509040b031c051e040302010804060e0f0d0f021b0a170307330c 69
    0x700082226520b8006c26680e900d14040002c0100010403540c1180004981048100c200d044901344603284003501080001ca1003800782200d000030801c40610402104481a0340c1e910700d40c0004521541d480508500b80070560744400e0200c4d803503100304803c024003880703a10790184041c100303641029402a1210300c1e901441c5c45403900354540c4101c84e1030a80c001c0007610740b402c50180c0280058581c2d4a882c02e00c0c540114811464280c01d40c050302e000600205040c0f0484080d50f0320302d0300744400701003048080c0c2281e070381280d01405850b10450b031513022441a25040c541640f69941d5a1040c48001101e180745000e01c0c03503d40e1020304c0305100603a4071000d200d8210fa0048404203002400e07240441c100b0480903c0440980300d8515007040c0540c0240386001d88003426001e603030490582e040180003509020300385907803100d070041c03050182000600b00c0310800e1030002c0403281050b00d0382e81c41c0384417559180b100607120044148410142d020f001b400c108003446000040c40002501e001c05040340c034150303 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 813774064 1250 813772814 813772823
    0x60a09051203100b1b0d020606010e1e06030901021903110901120b031f1109100c0f1a0103020a06030b0d02042004090c030e06010303050306090a020f030711011a0d 72
    0x400f240005501503500340142c000303909031650b105035000b103000548201c89002d561600504d05c5403a4014008140244101d80c10784645411100d01400c008400c50f0089a6003403034204518502101d840f010302461040788042c0005a0715443c0d60310380000140303070040a008140c1450485e19601c18010305881c0301d5042800c1c950305030b44d48460703140f000e41a01c0c40f44980501c540340751441051203828000261194000c0104819040201a500705201d03482082d90012404150284070a10072402448200d00a808290500100b41e49000100d80750b044031404031070918005200b0340c61300940305e40080c5414103081203080400701c04a8408150315002078802d0f6034807010650b212a803425040701c02203e10041c181d0340d40e00c17510540f008005c0410240e0000303107080704800d815100010024140e0707405465080c216034414040000180b0020840170915800340003120b0104070710700141d03002d5085501e81840b003000d6065100d084403140400394013800d245540040d8181c659200100006030007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 813775314 1250 813774064 813774067
    0x7060513050c0a0b12100b07060603060605152a070e0717090c0910090603030918060e010905060307030b0c0712020c2107030b0711060703060312031a0a1502060a090512 74
    0x106e4906d1481d82c18658081c0c0e204000c001103107820030150b0751000d000d9038410b01080140780c1d110740a000342110481d103000d0060804100d041d03152629070000f51140c807441c11500750030004000c07406041c20b50943c80907040301003000074800c015802042080d40c000c405654051a8605111030035a14491031654038000c10100c004180041303004840300b00038154408050044550300d00d002420b06041d0b2103046000c0000302072640350300c101130058800b100e00383c202c0302c9400d0f400c14415100a100c0945190b03414440d100300080007500070042140714841d41d910554480b0b4807420b00520b00210840701c8801c41d04190320aa045581e0007100b214091603161030000c5500c803c42219103048069080a17012030108002c01c140540d001c45842810071030441502e8160f100c0c502c00307078203940503408020501c6041d800c4000c0298443d07803042104986007a804868000c0e0100828198410f5402c41c402075408a4415034a150b010020300350000c1d03080d40f04100358603103512425101d0710a4180e1400c041c00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 813776564 1250 813775314 813775321
    0x5150408220e070906090515030115030213171b0108070c03020703150c1d01020c061c0603121b0f06090c090e01020d060b0a08060f040207060513050c0a0b12 69
    0x1c0448899001d0711480030101d4150a002c40c2c00303410310600d4400e13034000440040d40411a41410303840380040c0101c00c22428110303406e241009000001240368042016070910100740500c043d6050580144440c4072001621218031101c02c5c100321000c02c03009811400301c4100351059900005c410b501c82c92600d0002e03440da19a1500300c0c100703401580040c080c409024820b0020f641141e1210980840545504490514a101d0042c100310380c01006070150f00207c100b001103080071030082003000141c0d984895450b000d041894100c5849400c2500c0e0f032022048642c000507000500101c043d40c40c40c01d0980007440c19540c0703680000d14070314024070154946c01c2c280c040080d04044000913112141c024802609a5a0414000e4000b0824a41c0d4641010000100220180220307040040c076581c5151165603968103000701c0c60070340307150103401c541d0810280003c039200d445258000d03003040410390000c40c0d081c10400d1424421090703a912503e40618208505640c440448041d2162606048030681c0e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 813777814 1250 813776564 813776617
    0x506030a060e01050f010806010617070e130c091e030f03170721060509160915050309010c0f02030315040902060715050903030603030a110c120a05150408 68
    0x3501500101024280103042110203010f4000603c100a4211003016070b03a40c480241395590700078481c00c030100b000030f60b01500c114076055001c0d5002c00c06041c03020004000c4400701d501c00801c00180481d80d5960389203841d01687c041d540400034030707540481440f000c919950344071143e030451000828131203038002c02d442050700617032440c07403060504c4103803183c0c624040300043c00c5140d442d200300500d036070b0092a80e901040f41d8820312017030b01e07005003454080360740301842c401c100700101c60b44605214820a0004850b06c80340b000601d084115542d243e12410801d4229096842e540504c0b424481c00d4000c5a00113540041aa036102114544004200c481540403500904640c00083c1d0441400181c82c03042c84440741d0301c000c001000c268100519510f101e05640c0b00c0c0020345130070b60705401c00c0000350f1040c3d1181c240384c032080100c1d0068406003040c480020791143d50844005801b90044414030341801014802e03402705021810640340503141a644100e614451100070401c00006c5003548c07104038 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 813779064 1250 813777814 813777823
    0xe070f05100c0618030f0e091509190c0507060e0307050c1903021305070f020c060a0c05011e1506031a060309030d0c0206060f0312030a0e0a2a05091504050603 70
    0x22080000100b00130240c0b820001d114084c0703071026601280c81d014481310181420803034644650460201c51004c0440c5004000340c00c0400b814420010713a881c0302a0440d0f030440e100e92609411a9103139a50394408500d8801c06868400400e6605c0c0c0d04184000c902150000c12103050480040352125000804200c0000c000b8275103070000703900501011001351403103d1a41c4064090304a0340c580c2501d0040d58401203030340340141c50036550070a405201a1205a004850805619100303000106051942c81f80300d0318a010b039000030b01c1885840d4084500f40f5440d41800b800941103500c1d003071001c4540f241002da0610b44403100c07580200c50010010302810800c1c802c0d90300c081c0300d4200a008142e10804003e54603142901c3e110310800300e0388200d213480d2400050404441c08401c0c1c400b41580e0b00c00007180001c0c107217a94134901350302800080a001401c4010581110245400d544003024120006600c64160a4020328000e000d404144030280d0703120340c507400d080402264040342d140d440b03501007800d1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 813780314 1250 813779064 813779081
    0xc1104090c030b0c040311040203090c04150e0c0d0c08101406070b07170c1e0c07030507090f05010b0901021b0a09060306140903160f0c180e070f05100c06 68
    0x114043c2000c4c491203018000c0100300704c03806042c421082c824690100b100720700c41503540803800e038001541101107050540003030b40b0b10802c03060511030480d540c0110f0110000c0803a1405002000058000c4441d0180c0c0306820090318140740c148a60f140c04e24000e001c8035500d00400381c002043e43d0201c0c0d0180c6d614022146481c2e8841a008898201800050540c0d05055a03072800c504c444000601d40c2694a42510313008440b07081c04580140700302401100552004080f042c81d40528000800803400401c5490000c0c00002d00003c2c1d00c0e80d140320f403542110010307080101c05420030401420103a0b8001500089041030000e00102003550038000b40b6403c185501084445051080000510985170300014000540a02c1602c0d03a9480e8120720f0386034401e142c0c6000c2d54170940741d02a4080307565407040a0455210700008901140c645d00140400c11040c00510a071385c3d2200e10b030b40740041c000d018140080c55110707480c16000341401300082210301154040e10821200c1c00424081c03006503003040c4070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 813781564 1250 813780314 813780323
    0x11120f0601053a0521191b0201030203090109080307110736060e090a0b060a062a060f0509010c02210a02030405040c0206060306070c050c06210108010c0905010c1104090c03 76
    0xa01066843c1550a10b40060700c1c5e60011084040d46c405000e13001c3c01c852410a045411035952452481e07005400035040a400c0350f0f0150742c0d688503140042c8241c80110301540d942c1d105e01140c0803010702500d15100807600140070100e00700c03480d83c401680300b156421406800e1640708480c040382da041c06000f40752680c0720070024500c0f68280280480702042e440c0d0380314051344100b106a40c481c818413102c03001503c5948001041c02450b00c0b084112040c1c52402c40c01c40c420861a0326144d0348070f038000e4071000100803007515a10402d01030044424413502043d0300581c005080740400c03186180207488010621442c64810024050f803140e842441100d001e03000042081000361010f150007580d8a0080b00d440e4047e11034074001c03406e6a4001c48210031865445002444003031620f005000f19a0406030443c400c00006030005c1001d2960340324000c2c0a440791000008202020304c50080181150303a000e40e0601c4100c0c4001d002107034840d404030714003201c1600c011481010a2030f0102c41d040c4294806423 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 813782814 1250 813781564 813781603
    0x91314070801060f02060f0703020703050c010f060504230f0621060412020313090207030c0f0b0405062805130c06090509010b0a02060411120f0601053a05 68
    0x3032401d030022000da068800c150781d260b4141613083da00740d035210b40958420484580301000600000c0c031070380080c42081d11178a0003600b1304200b802003600f074400381c40e084812961100302c280300c581000e2003040c410b01c0f1006280010340c149a074609490010241c0303080e501d1198100001d00f6600e54195446681c0f8070011070061801b131028135140c5860080c0c40845a0301890f800440740c07a480081603642d00c2103081e07150310010385007001882c002d611030304044090013500303001038011904001c01f003402540507130b8800c51a0700d0640340003407c1104c010031224080e03500242ca403440c0c0c400c1c0d0302e208604604118001800d92620300410b5a21024618002d000b060f4070003002c50407a5000c2007050845130f040e507006090740d807580b4010b4454020b8001d2500103034460800900418441452501140300c05040b860a1100104500741020702d02c50001499510800040289003442d2030150b226100f4160112003850101d07042d80190302c40c820801c48684500c0b8103607001d01c0350074405403803a48191440003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 813784064 1250 813782814 813782821
    0x60b03030f0702090a0912051c18050606030102030c04031e020303070c140f1509360105061e0307050f03070309020f100207050402070611130e0a0c0203091314 70
    0xc010703550148900324054250400800c0d00d10344180141d0291540c450301e074040b840404a01207880c5d070020308040d2000142882c1220040c419031046908840e541b02c100709248a403800c0c0145800c00c05411140241c2c410410407a2054500d17007520207032a440110129084810480c2440010910002039403500001a480c401c0120742d205000464000313010442100c1d0790001009001800d802c0d0480c2c00c403480b980201d8a1860380d000a100c8080005c28101c80c0c480e800542540b2007121900601c64081d4140310b2a0083c1c481010741401050210b0f8141e00c0e04410041d480030003492640c259640c6040031001c00c0e817490040e410303988a00039400c1460b44a140001000f400f40170f001d0310981c000d03c0707a001e0007405420028a00380c00c14020307400602c0315524040c2804001d501803441990b00c980d0324281c0d03003241240d82005050520140c081c8014032402c0070300485100d44058100c0080500c0d0224010441d9008807d0356a44a412111444100500480217000c0d10382480d400c80320100072001c1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 813785314 1250 813784064 813784087
    0x32e1e02030c0c0f060114060a1709030301090b06040b0403030f1b06020909010e060a03021e04021c0b011d0d1a04050f0c010228030212040b030108160b0a0804060b0303 74
    0x1d4042020754604461802184c40c88140d101c110a0050000d00300c80d60311241c0c0c1070b0802c00300071b0124808501e01030000c451607080e041d03072000050301c080c403580d000040100003da0700d502440d10004c0702100c04514061501d840d02e02d051050f4400101880030300b1401d0868640110710702c019050710001200300c24280d40ca002c000940c020245184149001030000c640701c8200c40003030b442200c01520300041c25087d40c0030402c1e800e042c0d03c3c498903032000042c1024115251800a0f1090030086140c500c4190000b162131401d4400d10316003a0304008003824104a4003845411104e494202599054042903460a201040c0d01c3c0a291002c81c982501042c4000c1008c000340401c04031019006491540740034800498603441803008480d400290005030388000145081140350462090048984101801e500700802d034100340d00c020640e20b004001000f079028240304403844980441ca02203a414101811203041e400340c0307942082044605000241001010f901109450714020105c075101e0119440 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 813786564 1250 813785314 813785317
    0x3030f1c09020127120302030c06010506070201080f0601050d090f0b250e040b030d0f0e0102121206030c03070b040519060219060204030c06080402032e1e02030c 71
    0x31905140000c0c4425549030022911449549560594407010342a904620105195481c40800d44002c0891800040c1241ca880b0054882d00d110340c02a40d02c0307464100c0c0c40d03401d014059002c00c0c0141c00c1004000010b13070f403100c44294014a05c01d28044c10361180d07001207426009001884041915204c000400d00084840818580d440796201d200d1781da40e91100005400c1141108000101101c50302c4201c40e405450300902030700c0007400000f9903044d07071400240380001d008270503004160040101d00b80d00d5401048210303250400e0005042929100c008c0441900c01d08040d03141c011600310104046950a00a6240484004044030b07003c5885401013090303039010388a0140f0900c244a903e030801104030000c42c04541481d00036000f0b00d0315025442414102c40c56048421030f03400c0201200060119001c00044e11556454026030b282501c107040c0341c66081c040402070551201c00d401e00003008241c1c5c82a84185024020614a01a11307401c0350440d000510000110300210420019011260 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 813787814 1250 813786564 813786577
    0xf2208070506150102031801120906021c020a0f030e1006090510050a0e04060b0105041a07020414060907110f030c0d020c01051309050c040b1606061e090e070503030f 73
    0x1001c2c2c40941c0c89000740d40c00c03215401845240960400e029905000380c1c001404500c44034103040040c860fa1046510fa01207640d07401040390fa40703501003042c0d80320200340e0308504200140080214074008450101900801e40d80201c5420143c40d69822410b00c0001e01454140552000e002e0041c5604e4a070075102170401110f944050202c1c40c4030001e05450914245003c4440341c01c90403455496548405001c0e207801c1da203460600c0380802c8000b03030105070300f4000005414400220360f210901481044203459031070460164100c10402803000359a5803500568001c021824801d4500e60018142d03810004500c2e200c4e4082d01010802503050f110110b154156008aa4282c0f13242c0810f102c01500c2c6ca00402103050305504402109212012a584c48550003207003001e5001d00b0183d488035240850b51000c80381110000c1c2002d8207004102160040101030f1840321525240b1614102005000078060322401456503221005481005001c0c00703401d0107440040c06032a903409452841100980c4181d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 813789064 1250 813787814 813787823
    0x70306060f02191218060507110409241104060801030b0a060312030c03060504090515010f120f020a05030601061107150c06020702010e09101a0906030f220807 70
    0x18403500414030126250700500c128102c900c5441401e030300e40d0120400796140305814017038030421242c1007144011a040003480c00da036031a99900c4462810514080b22a2402400380c2c1c10a82808001404025840401003005250b02e60402c442895000504480100e043c002c210002c0c0c045092a804407005050300d000b00c141e9206a00c481e00c120088903200e20000d0705007881002000c4109204c3d401c41350f40e82c44a8900411007580f2030300014211581c02504480c00e41c02900d0106100111213005401050b90000e0102403500d04a00d550348009004001007201502a42240c11541c441480304080d09024048070611340c2c540901824210420a0741320701c6200d0480e0020309800711070b241100c425040e90321000b06512644e01c03900690052401203051210820300008951560164548100604144108110300d04120181000c441001043c40000c081000031800d403501412207801860001362030350240e45071140b12480110405500075500c101c100e401091050440c0a458014000d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 813790314 1250 813789064 813789077
    0x101b060626150f2a0a030b09100501090923161b031e030e0d020607030b03032a0a12020102120a1a010f021510151d1e060307030606 58
    0x905031005000038215003684072442c03035000240c00210315582c4203c0c0c50384039816100130240101c0c0e9104990f004020008000303550b8174141910b82c0340c010170568001d0512104103800506081c002440303200c1798022185000d444907080b154401880c1c0402256035415960500e16060008002050080c02c0088000144501c0e050040304103807101c10240281d8562501102e00c04850202101000c0d0200356909050303640c4000c01d82d082060082400059196000d1306851401003c06003c1740c0c240e4500074080d034414480038111000e415002c4001040204054029070003460240b0b1800e00141c0f00100032038184540410440e805402900c05e4001c1c1c00c094240300c2e503582490a0407903c00c0b000d940302c150854030f030045607540035a1850380200c110781f042c2c489422104030149030f0b01400752007480041c0d0b94a0710400030754100025a8020084600d402d503890300c0301c0d26079106000d5003040514032071201003801200c0c41c00078000c061207902c0c01510058076440c100d0005401031110344030b61008a500c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 813791564 1250 813790314 813790333
    0x1020c120316122301031506030305030a0506031204030f030306051c06090501021911150906150a0521010510150e19030c14101b060626 60
    0x400c006407441982208004203071094104000c031903a0700e4400a0000596441c9458443c2004a4080f124143c603441400685545180b4028590b92510400454113a1826105100103540036088070b0708021a194082015103c00f00004c2c10801d0459151500d8200001d000042100010603800070500a40b0108581941e400c1404210780b0614048056042a221404001240c5600659190740586c00050030f2141039010661500c04910200c030120741c0c184030703680007088104440421560790501c0340c0c2c1182404800955910f001500800182c9092809280c035500c40840701d400501e0010901c0080d00c0c3d0f4540c0025041720154010308103175003424002500c0159401402c022074150300c1440103c03050711401103a11041d00d4000503070000320703003075903500d0002101000009140944513a2082910f440a17240e20b050030900600e0040c3c4d83e035101403555542014810b0607942c3e000c059185a507400c0c0c0760410003013403140c03c181d203565074910000903560041c40406041c8034a02713041301d445d901c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 813792814 1250 813791564 813791593
    0x90f062703130519050907030b190e010b0a020f06010f060e0109030c050105070f060501240906020d0809190c0504270816300c0218150402040801020c 66
    0x400d07180e5030310b42d1001261041080f41000000010061418214080d03442d031520000f401c2e2403c140c46440c0080d495440b4020700c1c0c5003241d03841450500002e03500d40202e141c84116401e01c1d505208040042d0f1010071100d400600030b000c200c944450607419200b06603140e45585044901901803100000c100d0190010301e9400b0760b90800a80c0c0c1c00500c3c11185600c0c000044a881c2c1c02154211064465450303c000002c0150164601a28100c059030b40c401c8600c1c020380001103400070049040000d01c140c2040000e4001c01c0c103000d143d640c0d150103002542c803900720600e03084200ca0055002459040c0f018140aa428160010350b00210382c18008080c0c1605000a11088031541c0540c46110040c02c1c40000c1c0c0f008000c0c203994800b0340d020098660703261114608031814005412040345045400311250342e42c00300c0301c8014420360510b4032601160350040f03418040104d2840700d401c161000420300b0788201042548490400800641d607954460345802d01075080005202002c0c0702c0c4c2d00c0c0410400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 813794064 1250 813792814 813792817
    0x6040b030a0b0a1e020307081906030c080a02041b0813030c2004151802070c1203080f0f01030f03200708010f1802130902061e07030905040c090509090f062703 70
    0x605944d0b44600c0745443e078074141c2701300d4044603500f0340603255195400000100c0402802c0010700406029103400207050044c00b0650300030215222002000036031182106400c04006900320001e41004116041140b0f0700760340b00d500a840281c0300005100b00040044098140d8ad010f02d1410b880c140480201d4480b000c00052590050a42e11711001005208520155002c1c1003401d00418010104a41d54a06503030003016018061300062084020417408241950440390401008050b0520540c95500c62035a200c0074008000d04001c51100d490014040c50000d00c4d40845da480c00b6104800e607900d48660003000450391020003681042c0c100701c1c05c000d011030b4000c00160007400e403000c50510400c8050003014004022a48081d0520030301001e9010300038400e0071a100e68152079a150b441d401c0150810400e079001b00d00c034a0034080d1000302d1940c02903449080b42c209130b50400403901d42d804072909103141021744180742c3c400c04040000300081581c0d000032045940a5205114032a0281a6200d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 813795314 1250 813794064 813794071
    0x33b0f1014090d0602031017030406050301050d06062313050408070318120c0501033e0f0d021e0a0503070e03010219120606051206040b030a0b0a1e0203 67
    0x1041c000030340d56401e903907400010520120028035940d0303030b4070b204d41d283d800300e070015070b034880405040e54001d0003c10908264884429400b000441c04d2601c4c04100030414441402400e00480074102c00c1c104100316a04240c015244a000130000c01c692800b80e40c645902e03036001c480c0305141a80c042d02c0d00450760300c28036000d160026040c901c0c1c4011034030b080e10394507418081d00501501140c00080e0b88070700c02440d8030b01070b8400c02303008005602d0000010165076980410044143d44800c1b00d008282011325144030307a511034a18000c901c582040c04002ca80038001c10840300c0c00001441d404841c2e404d40c0144450b44003103060624110545031025000d01175100704001107141000807901e0340f40a58030403010540000c00152a1080300e120300d0381440400d012020100b180c00c0c070b441440d64040e028400151119203003031820295045501c0381c0c0300d40e016000c280241c2ea915640982c1d500c090000541b80c503080710080100d414241c0402c0d004041c5100c0c1c50015114a9108213020b11160080360300 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 813796564 1250 813795314 813795317
    0x1091202010f0f020f0d09141c1409090105010e150301030f050d0f08060405180f06070815030a0b0a1113080601140105030a050711010603150c0302090d033b0f10 71
    0x81c128842480c6004181c1e18900b48c6482280540080019008008203caa242c050100500b581400c080242526a11107070540b0007020500180410f6220350520504480c1c09207003101309003070741001107035000b10003802d001800040000044284030301458520b0119104104440d55825581000c585d5441030900d00e40c00204420040f41e00c0d0315160b0001908a0003c0b4030060205449071140c1740340c140718400340c1942e60421410440c0139030b00000c500350300255a03142c0c1e03418032034484006919041d000000038101c0360400c02140741408581e10044502c420040320703a90b11108070019188403c01c40c030642286200b040008101548940090700c5401e206840310744c2543c6030342c041c100180030020300c0001001514118060401f00c02d005000082d4003550842020400e20000c84090340c0e58100c1040500d401004a10400d0310342c0c080c0d0340b2495405250260358020200c0c002e41c005906040b0030810540e0301481502003001c07002c0144080300c0201c0d000c2c860717815680c003031010301d07011102c6000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 813797814 1250 813796564 813796567
    0x1b0319030603080d0902180106020c0f040513060518071e120f022e030903180b1e090409060e01051f0b0a0e100201060509092d01091202010f0f020f 65
    0x1ca0440d21381d00461441440140540c0400c0203850140d48006826442000142d03c025110865814030f0710b1080da03808401c1d13800b030100d8a8944041464100c100c440102220354960000f2064025000e411640c0690901a298696501e982c00150910b90003000300814510320f800058290750080f82c88150b07944404890a5100150200150f8980e452441113030380903000d1500281c440c4040708041440e8182e1030000d01320580b414000c2401d010320280d00800000080213002c0024204151101d00c1c4203400d080a8495840f601c0d4806809a080c2198100741402c14040400c00e035904541905621304008028070b581e4a00c140500ea20015550107261640400a100b07200340007000f0f001440300350400070300344008800498000c25041f1007000040c0d41d0350006115034a40108040e400c500303420001d1840c1d0f40f040d03441c80109200550f5915218041d001600e045e148290407000125400c019070780390340c400c070a8020307000e0130500c0c0b070400f1030510348000110310961502c2518900000340800a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 813799064 1250 813797814 813797827
    0x603080310090b0a060e22020309071205030f07030903050a0b070311211f030c080d2604020a03060f0f1b21091b03050c0f03150c1b031903060308 64
    0x1d0306c002d4240800a508540c401265400c00075a078494008565400140141d8a2618480c66030401c007182e0407111a0565000140010a80000640d200550607840e8955540d400749019120b0380700990000307140d4010b400001c014002081042441845a0703101881062a45040b41100e03102c1e00130340000301a002544541c00303013810107016511102146210408010b64101c0428524a90740f04842e01c07a10b2040a0211000501151441c0d468908020b68010b0b00d8265592501204083d009810b401c2d1a0000d015560381452820046030808000c00000100070101000381c240700002c6040c5130b040c880504002c50f010680c501c0c2c150040c9d562400d00f081c09c001c007401d0540d82214082d0781c1c15203a0034410081420101001d01c42041080c070121120f14524160782041c2c040c1800d80e103e01500301d00c403602524049207520340c19040b40f000314010369036001d005205000c1c0f043e0492404103104c2c1e60301030700c03203000004260b075a0300c4482d403043d03421445404800f175400c0d40c00010030491050021 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 813800314 1250 813799064 813799067
    0x1050904060c02030f0403111f09150c0f080307030c050309100e16080d1209080403060b010201110a110f06040c1502010b09040303020909060f060417030403060603080310090b0a06 79
    0x100c0b100b50b0781c510641e4548080015000c00e02d401903002503502d0303608107260b0045460329a004500240031146929174800d01d200d0302410582561003034001029000070a098071500c02c0402003100c0382d00164112628240d403d00c1c80c0345400403160007020a01d080d4078585403038020310680784118548402410020b0b06003540704040c00e804c2005050a00c41d0025a01c44543c0e169a0314024115103001081400c20752040102410034015440420914114241010416080c1213401f52500a000412807405580040303004210250001c0440c0c1c1d004501100c59a80c007058003483c040c6000102e403810403844020a840d0407050b1001003050b28076441c1048588266098955070000d0741c0000105c011000d804200c00403812681100001d0f030001d091007940c60498449a04090f003034802900030300302c02c0c000c1122481079000d040701d56014806039410030b01081048070003039640038030140452603070f83c6001c0c0125001951402c054454501010660707042620458809440c004d0540d80c1d610300d0401c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 813801564 1250 813800314 813800321
    0x20301300803060d0c05061b100908040320040e070609080105130f050a0c030c0509070c0b010605030c041d0901140702120901031d0d030e1902060c0c0916030605090105090406 77
    0x2040300c07210403817040055255200c0001d042c40c501d5240d40000103c0c804411a4100441c0030f402c0035089180110344000f01d4400c006a0301941c0d480800c0c0e556036a08100039a804c502d0703550900b50300038103184103440d01c484007059200840c1c801e40c030396204844d102c0780c205003a00c60490b05040700001540d80c89022510200340704400c24096000d580d8000c0080c1c4924200328034540040c2d40c0c40704000c8041006051a1014a5001049d4604001c10790200d03034400e16640c006200d00000c04c88048049601694514102ca005001003105d10300350706400c2e400c040303000004980000b030b15403800220b40004455040c081d0311825165015000e1100009290038298018186080c101982c8085071113841c42e020009101c0041c00724014a2101e005d41002001d407030b4155010749194010900040c1d04594201c240070358180d0480714603841d0501c48060618140900c00c40c1d913881a000014410003401340705503c04030341e21039582801500e844209000c101202072041c0d030f801104142c00030f00410980d60 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 813802814 1250 813801564 813801589
    0x50610080402090c0903060406020c0613050a1b080f011406010e1f05070b0403180603060b040603050405150705250b0604050a0902220501080c0102030a0f030e0102030130080306 78
    0x44c101130a1010740c2000c42e24001c02101c00701c030440e50004900f45030f000100f183c01d52003480e021004641c404d455843c10f44500140c000140b0540c0108140380141010306440700140000900f2551130502403910f140c0a03020900c02c10400c800300c0008203072654841c803007910b240040903205030041c21116161040311403011031071004000080c031102002510701d04806010f607019036142865444c140d080c142d04c900499000c001450301e4507408211210f00c507002c0d03904458076800e002420350703590b04010341010310510030040505815001c01400a0b00480605282201c0c010001c00001c3d0580c0360b4402101c00e2000036000ca61460300144c3c86e0b14064104c0b6502000c0c03e07901242081042e804508000c00b0b4000f40d16042e000c02c01030700d038141c2041c40744900510040b801802007002403000070b502c034403130f4404500030003a005e0b441c1251280290020038485803540021940c940c2d50f1301088040c2d40603004410070080c00c3c2200c202104004070307948210aa0441d0856103191524002c1024966080 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 813804064 1250 813802814 813802831
    0x210114060304060b041508010f0b0f150409020c160b2701051303051e1b0d080f030a06030c08010207050622060603120905030f0304060f1205150405061008040209 71
    0x4c00c000c1d0200d4803180501c00c4031181900074103c500b03092000140c01d6914104540170002c0c5001700c06000b59440b0b03076241d4850740d01581e0f11b1001e0010444880ca2070300c00e54100200c114000184804d284c0d00000e408004914145010340e80c031030b01c4803080c1d01d00c0e21550030341c10444442500030104101449130716440350302050401510f02003000400c0691045142e100b44d84c0c68000b0310011110801040f0391541184540c1c005d024010350400440003a1114000c0c0c0038012542404d21a04000c2504101c401500111820644070300d0b044902c60080c000c00d0104890800801c7c400140d24441402a6440c85502c50003074503182e41c8500147d1029454101216648502c0003000ca01080c114455040a9401080113071075036180d9450150441e01640d11450003030b07000e41e1a003002c0c0d04000c0103a0303040d110f991808030300307001200c14119000418540f06c0c03148a8503200c21300050741043d10b458070540d00107560500840c1e849c0c0c02000006020a04c6400200e0074010000c3c1c01403402040041d03200140 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 813805314 1250 813804064 813804071
    0x305010509040b07050f28020d0e09130f0b0406060f1a1602010203094903030b0a05271602071701060b0a05070506130807030e0a05030d020321011406030406 69
    0x10460404e201c581e414a50040442d8507c1c04008041d414071910400c16450b05020f1003c90038440071900c0e40c071006058881030000344c0301c03041c1003190794001107035242d40000b950411411310382020340003000288070b4100c0000711008001030320b43e00341c43e00075005c0490714460760810810310a1a292303141d4524049045000c10848100380340c5e190039000805045085001d4000010410740c0d0009c1c00c008040e0040d0752500344042d450991000485600f41070f490310b0086101d00d010340101e102c0741c130a908070aa10803540c030210012801982c80d00324000e108400c090710030341c9030105801d9440c1064040e032070050f0817100302400900481d62001c810750055100000b401c40e9109003201d41c0b070700f015a11800140000071103030b007400010058142c000180c94060b0018000d16070340c020040c825083c0003400e101405012034000c0e6110241c1200402c00501036035005001f44500039101d90100300c41440104a400010304010a61400030f8140c0b80c5028602c00c0e4903810b50304208040e08000e00172070703c1c80d44 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 813806564 1250 813805314 813805327
    0x31b0503031803010506042f0c150a1406011d031e030a18061b331d0c091801020c03070c0909030e120c0904080a0305010509040b07050f 60
    0x10100020b060401400340c030146900b10210030142510b001924162049007408403e000c0200c500e44030b00021811600d411001c100007010030705150150380100c000d64000c0030500c0f205030780c0e4141788511580c940001008240d0004940b18090f4400741d034000e0000d07213040384c2c03642401c0044400030400a4000c040f920307002014071401c2c0c000501c40601c1a415000070a1100400d03420080c5880301003040418030000608008000745081c0b09810415404e1100c12150307030910009801006204583c2c3c081011a10141c80c0900c4c890010003c1c508082803503c0b03101070406500003130440131010000090042c083d000c40030041c5200b4050204a880c0742139010502e1201824070017484030b0b19042026640342c18141c201981c16000981c02248594101a101c20010340e00201042091804940001d40c03040c6140d000e0b0329001c801c08905802081b04000c0c0403c2c040104003810f1a156030359000d205582c0c884c2c0a01008030b405a40003001c03401c8400109801a0051000d0071011a9442080d414400c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 813807814 1250 813806564 813806569
    0x18030311030415050c0c012406112a060a080709050a060e06030907051c0215040605032e030f06150b0a0534060522150f0e0d020d031401031b05 63
    0x1040700740301e07038021042440c40100510a101c8203400030103440c01c248070300b030000391030a5407030341812f41d0704000c07114090058181d07a40d800140c02c04592400b4002c50303201e240001018103450815554607000c104032000025032485c0c200d403003c00740d807102e5544806040e0740c1d00c24004160009001080b0500038008045025202d5003c20301c000c914030110369914110500500c9018000180b0410048a00304424001c064200c801caa401026a0307400c101c109017500940c081001c1c2d6240c8182c1514244240002403140d54603900c000140510b03001c101407904060200e02c2001207203e03a040440c0c040c010025103900600180810002101501c01240141e5080c214041c00383c00c0f20010031150002c0c1d60060154621079240e021402004000d400c101480b0703050b0380540750000091000d40c00c90180740b0140c910b5040b43e903051010a0b0280052445201240d441c1d069110180c001440342c10500e4220074170901996a07030b100f00b01e2000841d81d0031030f11200201200e84101c24504141200006040d8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 813809064 1250 813807814 813807821
    0x51e040c03060c0f0903110d0507122a05150c010c1205090105040b0610211d030f0f030406180606050a0b0c0d0e0a0918030311030415050c0c01 63
    0x540c410540034440c20304501d400000c541c4034440e44800c1044a24103105070941044031003050302e400400d804850360391940010710010081c40c0060290241c6000000e890134070114203105a48038081c58120641d02160300c4c16011a04c91900035040350078081003115041070600300c030a880c94544410324082c000505c080c2910a44045040025009001b800c150036261043d00e41094554009008504154076030203405107028001900c9081c80500d0300d00d400d80601c1d401c0c0203140300c96403031a140d0003050700100014400d580e1845402d610015540c858104040200ca04075085d69044604184152180e80030b2908010801c58006a0360007110340a0246191101d6595100f09000300d1144d003094107105809030260f0004007065024000038403003240c0403074a03d1250409151100070954080c00142a40c1143d50225491500d440d100c0142e144201000c40e50341c0340652003d021031900170782808018481190040e00d148030fa021512040c034000e070400d85d000380d0310250321800d0071710500120307086 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 813810314 1250 813809064 813809071
    0x5031b0f0616120e0f0f010f0302040515032502070303030908070803100f060c0305031503010b0a0305030706060f0302030c0d062003040c0905190e070906060f08061210051e 76
    0x1540c41c914041c0c1c0f00c40c1c0d40500000c0c07032100d0642d40d00c19075003039000100d44102064520a4140907610306540c9030184294180d40003440010030030340c0d164481a401c21455801070b9100080101c0080c001519510095054954150603500a107105403175620102e0080c24020022254100100310020214907850701441c00307991103581e015407940c07400b404440040c00c0c0d41c0c08841840f541515020210341c20609880d80940b10001c800190500c035800030380144000301c10309074001c446030310200c140103001014040186c8a0003003041065150001a00302012a1200951613405a800700b4181e090010800c3d482c98400c41000c44e09110101a02c59082003034480c10300c01c20800300400040c044a006180c00604640c6020015401c118800c514018090805003c03100c1d100c0400d64071151080000704010701c0d042e8010800c290300c804000788041a8042804009114800460424500f08141410b00b0390700c3e00082c800001c240003941c0151000508513941e80180d40d8046501c0e5503c105098030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 813811564 1250 813810314 813810323
    0xe0606011707091d1008010b010f08100503060c1209070e070f14030c0a0915050712020705030a03050406030b0117071404031709091f0302060c010b0d0c080705031b0f0616 75
    0x35141740140c01c243d560210b50307004128603810500b0703141b40c0d6600402e26008c4400140b40a55a9a40d110a08000c20140d54001a0148507080400540343c0003000078021072000200c400a940c0c8076035044a0b91071440e409411400e00003400496117031409129511181200350078500140030000d00040c4494004803a030100a03513000800e80e8480394481d07038541c003520280410440d880e44050004100d4002c0d07020003403481e19074801014604e1b000300003500083c00014100d4400043d1442c000f80160020320420380442d0500002e40c00c2c2c3c7d80240d4080b0001e43c8802e01000315a41c0d00002220102c2c4002990a00c240b01004003102280e01790080144100800d2802503803903a044050189401d0000d100c0c60000c2a40324007211103c0103070039070a080782e40440b440fa2325155001c048600405401e0010799014020300c0b045000c000a2003c0c0804075107850702a00c52490340c620034075448840d01c0c00780e442c5103d2180b000036171500d0811083c000d24900504068181000e100e0304c41c146e0000000b0a56 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 813812814 1250 813811564 813811619
    0xb0603010c0311070201110f030324041808130e0a05040506060307210201171003030e0301020c0309120a080a03021206040216030e010315030b0105040e060601170709 73
    0x411810240554860207260b0b01d800c1240f507001c40120382650080341002070410020551403500b00808110400f62030b4146410f407590307410224005204540c00c084040505481c00c54002400d103464810003d210422030307002180c0700495174942c1501d6000c007003031400d100303e0785901140c00020b1080c40d600c10018000000348ad8185400c08501d82600146070911951122500707001d1081c1840f2404007030441054801240741e02e80c8016520700410a5500e19000710030b2003040740700d101c07124040781281d010340c41d1014024900020706082c5d1143c0101084242d2023044100b801e4185428014403030403a81c0140d80741c00d4480d035150005076004c050281c0001b45c01294804000901810944e04018219411450300000001a0190f00320703480d800b0b010301c0041d0719002045d900a421181c0147c5201c445244040c4d12803a2600c0c50070000c0c0107042c01035203410704500a10400041180c081c00b0b058540a0403909034594240740c540b0b000707000c00100060143c00181d501070108524810104801000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 813814064 1250 813812814 813812821
    0x1152102130c03331802040b0304210e0d0b09010f020a020304450608030d0606022103040b07030f0216140105010b1e04030b040308010f080f0c0108090a0f0b 69
    0x7962012074881c441d80c140900294003e139294110108203040b1030500451a5260200c208000b0080c001e59200d0181c020b8004200700030490342d10140c20b200f025600c800c407031040c091082107401c003c04406c80c981114001000f0404184e40300000c50307101c40818008600218492181800d07a0020541180564000308003804504040c4207030b04003030035000b0440014880c107803012000900b0300c56001440380d06041023803801c1d0595034000c44060003000c4201c0b0f07a2240c034510b101e001045c407841000018091500755200075641043c0010140480074003040c1151240d40b2812a40d680107804001810381c0d84803000000c0c00c160000c2c0845c801280c81413600c4005074103055003540d0522541c40c500c3e900d460014020a2081c005407003495500001085000941e280c1000d200e10498001800f003600e02d008000030503a000000c0c9045c1c40380034580140c0d1590742c48046550780e660b000e0111240e0008a000c00041d440b444400380e2101c00f150484610f0f054580314030404002081050700e80c41d01da102003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 813815314 1250 813814064 813814091
    0x9060509070807020a0305032a0a170c0910210b1c0b01261e01110f040308030402040b120a050c010f02060105090402032d01152102130c03 61
    0x110707800180390400203010315000100039140d4046040080500c600403010031380321212040302c4140300b101410360008518480300da2a0240e00311203419000240000c1d00c0005c40e2501a0b06103000ba900041010f080c9030000081041039201809003408100d0950315910b4006c0d41078420070311241800500081c843d21715030620450841d115100c01241c0c0329940100001001003c032241100c101e4500d01c070010924102580703003410900c602070020b110394404468019103420320b40f01c1886c040c0d0000c02c801c489101c81c0c1c00c50703400340d624030030440c82e030a000820100310240c0c02541d0042c4001c000180001c00c00000440d1a5034400c400b00c642e5000c5100d10041181c10441181068002d0030045503500041c0c100958401d41401668001c038484404201151420042c1080c0d0300a17030b1070080307009158402600c20300100c5210040c3d0660078507003040d1404010400003400c0e038680100b985040c840040304003198246a440898002c0c600104202c4800c40c039201d040820101a07a020a502244286 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 813816564 1250 813815314 813815329
    0x10020a2010030c1b0201080f101508090c0306010501020a080c0c0d0503031e01180902030c1809070603110405040c02070b03150a080102040b27031c2d180807090605 72
    0x3100c00d08158a0052a80547c2c0c002d0039141e4002d51801e0358544d207503101103408200c81c60b0b6501c10344080f00d003903450309034041e0010350342c1c1c3c4035407000c0303003100c018003a1b110406590741003e110f20360140c2c11404115000c24150401082c42e1800c800840d2603480c00100450b9210300200801d84054001006010346018440440310150300e1005804050f94104281001400b00303480c4006011b640c0c0b91210011914213212002c8034400040c90f00c4d0480000c100c500058407021101b941c048d010700303003012070124064865048094141500720f030402e41000140301c01045805d86a105511402c2000aa842d0b0300c440214468401d4105450603070400750144060b00c01c50341c102e80325590050100740551000c1e0b00c191070050040129900030710451004800411060000e501e80502442205004503094261541c0b4404502d03600e00c1c0c40355065070b4421225200341030682c915400c5442c1c010700741034800e011401d082d01c42c00300c06000d00c5617103010b030f107180540552020040030b80340c103020005468081c9 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 813817814 1250 813816564 813816587
    0x7120207060f1211040803090a091125051b01020f0a0803072d05030f070c05062a03090606030d05040303170a09060e160510020a2010030c 61
    0x80ca6040c0c24144040c081c00180c1040404010881d1840c0d2429030103a0454840c849190602c40d9075180c884168980344d83c400505540510900d420000d40348103d4131600c1058100c210002e403c0100403a0780369409201e105400301c80110201e20440422400e0000b8000c4115020380341e55407607040c1001a0130030824684000154100820300c01c0400c400601300c0c0c2d8018058900346061852010541000041642c2d030060390440c10302001190a400c8001540940c2104140c0102a59013003030460703e41d600008010440d0704440007107210020480861043c2020104840541c2d00b041010700c591174004454010040d8442d40c244400d504041c0030400518400d80f804625050954601500c1c0080303103480c101600f03101100107104010580e0101131565070113001840024110b0182c507640b20100f04484680d40e506000010305403070030582400200c50541c0150201101035111b40c02d0b02c00d00384108000204072034601c1c03140c2d0741c3d82c840130850b104030766180002c407807418480c001c20418509 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 813819064 1250 813817814 813817817
    0x6030c0503071206240806060319020f1e18040b010b0708040b0f040f1203090b130b030a09050a0b041709060d020703120609090b060a2d030b0c0712 65
    0x2408103122480300c02894141c850307006900400c030401740010400b5010907500084000144d00480490114404242c1034050a070480c102c41a03881000d143d1090003e81d04802507129108005210050130000800c1c4014158502001000f41d00c40c40841d1102040c2180b01000e201c1032001c200c10403000c4c400550141404242080c10301c00b0350b607a041d00070b11030340c01b03640c00465003c00c40914104002044070090044918614000750380e0300c0c0c040c0c0e441c000104088000c82c10101000c1100b08203031050701c4122100404c0e03484e000c1d1030119490810350002c1e00d0700910940320700e610008283d0402420828a105614549261038981000b43e45c006144d160f201140c5402c02403030303516903a90f400351031041c2402d880040e550079252070103440180c0520410702640e814030900181c42c040740c3d840700c0380035070007a40402e00a540b12420003070144454012260603041e165030760410910f0624240200341c034840a00301c0aa52a921030b1845c00d00100da6440c0c86c844006184d104020180004001c001010b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 813820314 1250 813819064 813819073
    0xa02150402010c0f14030f030a0f0c08190e030a02071505030403080622110406140301122604180c02010b0904121b0602190503041502072406030c0503 66
    0x1e50009015180c0b00b075000e8103072100d01911340103102880105005c184440310449a44503046c1000e00a25041141d40355000c500c0c14580268904c094082c01c1c62407405960391000aa40d150070340d030188003081c0e149440c2180d81f0303400000c00503410001001030343c0c0303a50014083c1a2620f400000d48070800908002000018000d2000107a00720000700c2d00310404442140d80500006a921607100c0d210b82096103040c28201a020100302900080c0f09507200f951318030310207805001440502e0311080c4692075001071030120000105070b0746540100b811080004800c03c400c1c0d80804131005801a4110840020010400c00ba85d0000c40c8102c0441001900081c485c00c0308006c009031190130000e03c00b409003030f00e0a803840c042d81e204003400040c5120b0034030080c1984403903040c600c0007504138000b48010101410310711200b0340e0280f000e40b44101e500280702d4000e80c2d1400e424901a400481c02100c0140d03180c4140210342c00c0c0b000c4140224859404000785052960074071414890403540b02c3d502a420 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 813821564 1250 813820314 813820321
    0x5040501051f080403111b010e19090b15040f0f15020604030f05130b03060922030f020307060c030e010b0a05100e1513150f090509190509030a0215 65
    0x6250140c54840245061150f62079907581000c2d43d540b000150403429500850180d86021090918603402c402d400f070361100c0d661401c0b08203001050140b50311f80724010111100c00c0280c0e50941d04080c01480010701001141104440b0170b008640203a00310203c2c41c0f80f00c002c18890010042020002082e003c00d0449a40c200c0200c080d485150140000c2c3c200501c242485850034021011505052900c001c2205944e40e03030461a4450380090720300900c600d0300000400c00c0d61b03451000026000440c4038014010062507a01582d50f948104216400c1d804248800404a443d1380704804c44691152004100c0c180c800d5205401c6928202c0d11512401c0c8000040c005134541c00080b0040c00366900708464250004400110510010f1140385400040000c0329a800c0f28420200e000f100c0701801100420ba01c2244140c9040c003800e8210f00001d840100c003004945000100c0540051261002e20102800401660b054a108580d85a581c1d0b00001e5030919840c1c3c100b0540d40c003c03e814100d01c44174103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 813822814 1250 813821564 813821599
    0x703090b0f071e03061701020405010f0f2708011d0303060f0a0e01030f0c06080106210e06160e180606030c0c010e01140f0423010209030a05070504050105 68
    0x101070003070000008218001008140140a11080c110518540440068020744001c000d0452030181c280204c1014201c1e0406a41c1402994280c60b4140c40e28414034501c2380045441d0100c03541c2c101d007005441c024104401640c000014003e1010490488030a4200407140e400e480b440c070640f00b24400040c1c05043c0440b008001d44e904820200d60702c0c5600c0980a0004034501080c0d04000c0d8240512170001040003d010000c0c540319110311611459161703034601c242e420344030034480d640215240d80b40001c0c580d5604900300d0b002c40d1040e0f0000403c8032441c142c4514200701180c3c5c9941d1180440442c1068039000050500c40f024200c0e0050b19140c18010303ca54411006443c1c02d01401000c07002c280c0181c00c40c0196035603101000c0003041456114207409010306200303074a2294078110500810104030920841c5445160880c069004074080442c3e2700b181d45092200a01ca03e543c00d0000c1d49296406000d543d0000b405076000f00400c1e802d0504000c04c43c0c1c0e0690080381b00c1c60030f2254951204 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 813824064 1250 813822814 813822833
    0xe2203140408010c143402090a0903390c0e0411120111042108070b10060309031e02070503070324020327070306050f0702070b09030a14101b08070309 66
    0x200145412440c200d400b4032149642240d1b048000e50041c10369041088c12816a40b000074098001e58a03032003404094150340203616001e05031114001203024800d4540c0d210715078800138681c0b00780d46582c4420f0f0360f42c01c2000702410a490031a032060300052001000c1c030700249115000b4084130001c2000b1314108519001074070891107001c1030101c000f5003503600303002d414010050280e00a07a44076902e040b24940300f024131404031005440c852442d4004580c0910030301c50020000d0740350b00c0d6011046010b0710b4a40070003c0d00384481046110780c0c07038040741c02e8038207004400003584540c903401c2c0c080e18a41c0c00d100400c07060070b80f4104954414020404001080301040e8545000d00382656440d00304002c545d802d05c141d940016000500f80b5092150045402906504c01e0400790700350341074140c84241000f080d01c111910160b040c0d1280b2114400328002c11039140c0f080640c0000c641d660398600c1c11250548507034140002c104801300c8100c40e501908204410390000180c80c0400182c01c09a030750340d415 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 813825314 1250 813824064 813824107
    0xb09101a09040c030618051c0503070c150618051b070f0804050907090302120a02063004060912080f0c16050f0303100e2203140408010c14 61
    0x1040c01c1004203050010202042000e0750300400305102881005020a80b4a4107842c0304031020300c07a00e004a45083d03203820003840100c025a0f1000c1c0307582c41e24401212094205142520441101490000c00e1541481044000e005080b201071500e2500d880750001c840b001051000c404e43c0b0004130842c0f407002c4100321994985e000f07111401545a034104280346006541010780c000300070b081448029504151800304480c400c46002aa181c24541021380390076011400075040030047c0314002030140c07104800030301b0b0640703840701c0040e000008481058950040e1400d503081c0d95030340088014040280c0511030f1000d141e00b4544024200050034060441009110701007000000c513614030b4100d00c0c242415400c5801ca411a050b500f050414a5160350042c2d400701c02f00d40c00903400140c4c242503128494820390b8001a40243c030120302d0300001490622080c1107013004004c46000d40c13014096009040076100000000a11482110300a410020101d510401d15035050084041d011158504a8036 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 813826564 1250 813825314 813825319
    0xc070219031e020411090f150d090807050111040b0307050304060e0a03030c110d201203040f11010507080d09050f030409050f060609030a080307050708070b09101a 72
    0x311284540300280e500112600014100c081c90003214904120484501d80714600131901040034151400e14124244a902091a007007450b00d01e00c1d508038a095000780c00c64004800800340303418802a086c000b00c5441040407501c9200104895092200c248100c103022058000b199181500341250344110b404010160420410000b00244c104609500b0044504000390100c070244042c80c90041c0260428260080c00100900004281c0d0880005c1280c00c1e07900b1a1242c118442d950901130100d8581c030601e0280c18841d001c1c4848002d5210307001184983d001e01440d40f658030440c81c01384200c000c4400c0050400005100d0310300032540d81c1003250310380c1100003800100c100305881e10a04140c100340800c800703400301040003d40d02c0a150032107032143d0030307005648030f03035540714800c00c03016025074605150141d21811550f400600e04400a54001815082080c10858180d643c82c4441e8840c000c200c0e4072430700c0d01c420f0004031202002940364440d000b0406010f4014050a1100810310410100c1d1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 813827814 1250 813826564 813826579
    0xb12160c0b041103190308090f060c040e041b06050d0b01050403020108010e07110115170d090e1f0b120a0501080d0e040b03070e060a15080c07020103021306030618050c0702 76
    0x55195408101d240d4010040071100c5c04007440c0c5c0d0401030030b00b15003100c807503680303000b18038415400c0c4401198440c46200140e12542c2802e00f002c45808082000900031101450344500241c07203a0031448400f0300400c556518250f032088200181ca041ea24000c4009050010a000a00c0141c0c1c000040780e05541c4100101500c07a6503400c8200d403000c880c408103051035440e01181c480c41d81c40c049900e00c103844800e003802c441190003d0503d42e403104d883c002036000a64040041c4100304603918895042116503078031000c030b02444460034900c070301c0c194003401c146a00040d461540d800328003800755204d41e450f9020010380d0300d400fa070581c940b108010003900300403910a11000c20796640c1e00c03119042b00c0c040c0071240d20340e84505038000a100165000d61059120400000e001d090041786540d0f0b41500340c1c1c815520b0b440e00c5480f0095500443c0040781415000e02501c2d10486000d8914001814540d50201d9810701d81501030048000410164580e10b003410104400144d5120860b1000341c1c0c140d0340d10 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 813829064 1250 813827814 813827843
    0x108100b04021e0c0111040b0a0806190609090e010e0c060f04090e151b0a0804080d02031f06020d0e100c0c09060302030d032c01060b12160c0b04 64
    0x20700078401e214060344050701d40030082450000101c0604849611a402000040c0c40300713890a001d4016881152000942004440e8001d80f148e040d01d03410620140002d540c9040c0c40b604459150b40c40e800c60000a441884100841d45103402540d00c0600e400008000300e10000d10300c640c5a400c1448550b00901000448600103502942290000c00055804014030117884140702e4580003801003000d4030031134120102d41c200c001c12003100741c06040c0e480d00300d203800059641900c1a400003041940e4004007444800c5548950340011803080040180d2000540c4c240d448500400e035a540241045601240745406400d0704894034105481c4125010b084411401d6030417a41b10803a548028500f030800340d0000380b5001c6640244064074400ca00b07980c52400c414004804855a00802520011502c1046401000c40005513840c00c049600049819900d8038558600742d44150390b801c00c06800da0080009a420300030118011810504d8404068141c548030680310207001381000c1c080a030054080d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 813830314 1250 813829064 813829069
    0x8030702100e2d1002030d0b100507060510090212100806060d0305030c09190612180b04050f060115170903040509090a0f0c0302130b150c01060509010e01050a0e0108100b 75
    0x400f1240e400070704901150403802e40003500d03504080d50088170142850601a000c0c070f41074102515080040d911142011020303192400903140150800c652544400310100d1913080500007081c01d40d00380c0f0031441550034900c181c0d1801c01d070780340d0080440d44c011206014880d0f44480112011130b405180c000d840e911440b40d0213032988174010b01d480d80220507454492103508040c0d0350000b00d84840c0c42d0030b10a000c102841c54141c440c03811004220301c0c22100401d00040c02c540b00c054105000c0d00c11215400b80d4048883d2816000380c10040c0310117125904910183d078821400355608820074040451401d010340425581e00480c01000c6c8140d0304000007d048140400c1020040754000c50480304900e4113040c400680f0f48240130603402030440071790700d811442c8c0074041d1800740007007d42661203110a410080441c1c3d08400344510a95403107040021b0300d5917643c1d1000d4042c01d103668201d45130b0351400e01045141560341e032000400701103880c0100320400000c290307074a0b1400303090008140c0d01c5a4200 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 813831564 1250 813830314 813830389
    0x310030b073b0d140601060503090a1e020a0e0105030717030415021c0e010e031b04150801020309031b0a0c05090403090801140103140f06040f05070f08030702100e 72
    0x41c40783d04a00801c1c03d100c1440107100000060000440a981569032281c908641c0c500c0122040b5030550b000c004c1300c1001a5480520b50301580701aa000c00074103100e9030000302181465401681780b00c60040060000780750a2001400410788615100c0902c40040da000342c42e8000d42c82404035540c4a52498071761035000f44035070b06c1140d403507454084528400d00c40140c03910a410f00d807140015410404200242000120404c81784039640680c4081c1e41d808040101078100c100c0d40d81e505070400e0000140d6035800740003070740c041c1d403482c0d0103035440300544046800441c00000c12001d2036441415003002003103d0340ba043d01543c40c260740000b07143c5c0e40c60406031141c030034940c0142607030340c030f0005443c00d0b054400d082c01d81668031901d4841c0321800610410f030758850b01c580026440c1e80054010400044d080c0c1c8164100ca403242003a1156140e9803c0154050282030b07020f11281e4000040c00700031481c0403d4050b10061b66030038071402c1e181640f0b0100b25400d26440000c8803130840284107078a001c21580 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 813832814 1250 813831564 813831677
    0x40f050609010e0d03090806060607050a1502091306050f04182d140f03040605160f1a0a1103011409190c05270d031b080310030b07 58
    0x1132003500f880d101840c0007083d000720381c0300b41e03140b0740150790210741c1c546400421a400300e500000240b49000c800d8403aa09021000e05800a0321513081109000c191074500001c82d003a40c034404005020740c50403050050b8851507041c69031082c0d00d0510100c61001c4140c110035171b480c1e000f0140381e10701540b0200c42012515460050340d00ba0400302c6007001000040c803001c0781e003c800b4609440910b40039007406542e034040c0b402001e01080003448807016440d103180100583d980540050000c60f00c5a4548400300c4018000c0784144800e5102001607040c050300070106c51a20910043c3e103158134000d4070100041c0c0144c4801c0c811140000800d600141100380c940011800308401c010310703042c581c0e000c0c21590044520f861006501d80e400c1c48511741344a0a144240c601528911141005a508449101c20a038401d004d00b0311404102022030070580280d4860b050252041110b18118105980c040f0001043d5804010540c107130114400c04010142c0310181784040040300c5e028850030400010080e04 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 813834064 1250 813832814 813832819
    0xc0621061d07051e1902150112020f0a090213061107051c12030209010e03010204053d02011d0f10050a090b0f040605011203080609040c05060a1701080102040f050609010e 75
    0x60384c180c1604552030009081030604440d961707400f60b95481050741c5440140d001e030392200300310000411680e801059814001c1d44010030b4100404450030005400c00e68a4201e14030b80b82e40030070203c0006003805000405840c3c941440803510700d04108155440d001c0d8000d5038003172018400e100e5a495161442e10048613030101aa140170784140e0782c000e0083d040648040e0006050300ca154649003010701c01c8405a94014181c2980800340c150503442c50800c042c4081609107002c09600e10001c145e10001c00017050b2075001081d80c0146038000002c040cac3c001d07140c0400e600314403031039000105d00044041340f0110340e1030040ba40c0e40d103240e0707640b0085c40000d0b030240420208500b0000882010140b040c811440303500c040207140d0301d44020021101d00c002e0300a0100d20140d01181e00307844c20310f515960051140b42040300341e9880c0c40106617180c01103a801004907804010700e843e43d540003c66035025026890003107007490b180c6041d0149206203840741500600c00050b03440e5850344145040c50040001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 813835314 1250 813834064 813834097
    0x120608010c0c020906040e100b120607180f0e150a0b0703030212010905061005130f0308070b012709020a0e040c08010c1e030507020a0c0621061d0705 66
    0x1500c8020b00410b0300c050080340b0443c0d524000503411701d41031069401800024000342400c0a894a81c00b000f00008800d80f80e2003200f02001c0580703032200700b00301446000a6510070300c1064440500040402c081d40054580084242c410711020940e004500c0d0311800350310684040c0c414000c04181e048480307070091204508005905c0d424960942c006040c49800c038112000541c1c3d8a0710303410200c40054070304030350041c45080c602680a11031001b900090a0201c4050800c0d5a40c2d0301403800000e980d44110b805450116442052101d042ea2850040c0f5240d100015480e00160002407600c441c00300d12003142d5680c28401c01551903407a1414054191110141c459041909001071704928031b2156000075170821003030844251150305040009110502c0b84075400510f94000d03000341030001e00c40011441034244403004102d122803860000d02654546005c04290100c0c1e0013041c4406a40300a00d0310b040403010048240e00c80c854800848544c10b06039841c2e224024112901d101c0c1035000c8408540 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 813836564 1250 813835314 813835331
    0x1c050609010c45051e01020307080d0204050901090c08060901060f050714070902040f091506030509192405090307021210050103030e011d0a270207050d020c0303070f0312060801 78
    0x144003246000c1d101d04a0b180c81d581040d81702d0040c07010b00554807803030058000788019400601c03042c0190454134203620000d42040d880e000442c4111900744e02203403405460340c1229540c15040040700350000402d80c0c520255605100d0098070001d565140c02080043c0001c0c258240030301010b890100b6003008040d55603440d501c60090000c2d400038064010110444000040c13061450311514000d5842030740c200034400c1c54650113500a040042000c4140c3c05240d000810000303120f801412086c0c458607144402010004849112080080484078518a0030081c418503290000a544c61903030704540c907601d600e000d070010301c0c02c0100100901600c5801c201c0084105a00618203503031110342130303a03080e04101000c690501055804443c1e6604011036000c1803240c40f400e0000c040707140e0f10513256010302ca40c03400b1504040307a000c0d98064403544c00c03a180e51240b446d4140101c49200d8001c400450414806486000f4803007400704004090040000c1c403000002983e0b00410300424215000301b00b681d2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 813837814 1250 813836564 813836687
    0x603010f0602070506030103120c060209280512030316030e060708090d05090d0f03030b060a0806120a051504030e0907032406090b0c03091c050609010c 67
    0x180350040038054007510700041858104070007036034100c0ea00410040000404c42000303552035200c40d18240d401b02c0d000c000c0520640c90740242c040354858030342020b007021841d5003602103151146411482c8100e41a100006080a0000a50742c00c0020056002424001e511040d0f009003d558110f8059000d007208001c1195040849240315018040688082201c1c6c401c040b15588142c50b0000d601140700171a100102c0c1c0c409102d454100d101c0e05000070841104000102c05400c1044188001030a80041200030309008030501c1039040e80300300034207010f08280d485a07210f044903028070049111210020341410320a0300300c030780340d0400030f00740792120705141c20001d000d0300402e803000c01c0a00030f05194200801003011034030201e0300ca560304d01c0c43c00c904055201420303512001c80740c40680300920101c0308503520030640c80045650a40300030482030440c0740070790078001c2c01040302400e41d141c144055906c2c0e030402c600d80f08207581841030044111011000c0303203501c2039650609840b02c00001c3c0342c12a2031f = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 813839064 1250 813837814 813837839
    0x302160b0c030f340201201305030c030303040305160b070302030a05160e0d140f0d080109020a0813020102011b0221040b0d0513080c0105010f050607052a060301 71
    0xc2026111400180d0b644007401c2d52031180003028203082860300b4a80e00c134003590b4003012101c180303d588004904480e40090684041620400c1341641c0b400002e004120482c43c440030100400d0b054020340194059000001e45a000040003d82070003c00a1808003800d012034a030044c03d82e01113407030700b0241006a402002500200c0d4407100c2c9030b1404021070250229a145000d104116544101020701c0080034080d24851022003210140366101200c0498803003032002188106448008001c49400c0d918000c240c244182c1c003814545104100c01e00c141c6034000800b5502c40c003440181500b581480c40100e00411041105040d0044142e14000394903501007042c00c9205030312010200300001e10340c81040c031440b0714032483c4031000c010400e00000100682001c0c0c0e004800c0c41c202c00d5a02e860744c032009080d912048030340301d10340d640e40014005524150312000192106440b11810a0110f80c1c60583da610b544e910810a81c54000042c048500c11105240c21040043c00c260f8982d6580d45001030070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 813840314 1250 813839064 813839071
    0x303040308010e01051903030509042c1c0906050a14071b14031e0f0f031e030c0909100b07150e1603032d1205060105040b0403030302160b0c03 63
    0x76100f84000102071400c41c0c1c030310b1281e404020f2440c40a0f0700d540c1d0700b5141a400480881e80280d110542041e02d0b241503611088810f00d0300702108121920300341002c3c10100d001d0400001c400690350101016076000c1d0044080c7e410a041c078556034825203c0039240a0405103c910b40e04600181040130030008043c1c0c40d44030b00000300c1000d0503030b03182c400b004038400400e505c907130b01540701c001020380d0460865040388080034014113840f8a04a06890507040c000400c11124103640001791800c801e0694402100344448940e07a29402c42c04c0031022040548035030003513240300d0010007011070401010210110001e100402c407176540c408a902c1d10041e540007021042c6000e900d405c1d156400c284001c1111041640031000380184541076607400e80d0503690f0046503a095100044000c0305040000810103420300c1643c03150b02140b05412040c0d419100300520060401805003c1009040071107026541501d5040c00e000d611781d180c014031207008860b480e802600110b02402803210f02d660b1003009502 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 813841564 1250 813840314 813840329
    0x6012c0112061b05250506040317070903110103051005060339070f06090602030727080619020c150f0c04030224070b0414160b030106080612030304030801 68
    0x1803551550f8510a2014111228010520400c10803018000c0b0280e0100f551000e00140420848292195454914101d07403c9011601c07022260b43c45c0e07410100820b80c0f01d2040d1508408035421a40c82e820300c4401c000b6024103054a0300c011035821500c1003202e1000d8900039141c161a071421440c2d18000d02c4052801d82003040203900d035082030080480049101c4481c912004d0320b854400c0c0d40d4040d03a040c0851054500d80d82d10420040091014001140110b14030365071551181c103a10b8020b11900500e02c1c45500808030030708204000c0340042011580800c0480c00030417402d0351329400d00081d00c190713400c1e12000d00480314a00031140e08024560301540c7c181101c21206c2c0d458110300b80040c415800013940c800132042c40c20146c004604c46030000482890003260400070140d5690f140c0d07800942d03086075072401d2098801c5214004002c2582004400081510f07042d2800500007010321041c085c0c403003040701620000c0d00300d48800f41c10408030316010b42225540d07c2d1600f80240980d03804e0240d00c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 813842814 1250 813841564 813841571
    0x311010c0e180903041e0308160213020a0822150603140a03020c060328050a18080d180210031e0902100804020a0819050f030c06012c011206 62
    0x60015407802c103070500c942d071004001e501d46811700510140e00801d01c281010300a08806020000804035400752201241541010b5009911481040b51143d10b540c20881214030505c0700c2c1001d01d0b070160020707411401441c980007000d03901d5203c03d00c5100640b00081e004c207030120340b40c000300826680164220390007190303007003040c1300368072802d9407524481d80010b0010fa024041c043d6445c60240000c68204007962101410707420940303030003691000100010300c00940e84200f00441c8015a000301440aa214101c103512040705965002180c050003a000c0b588958802044540460b0b014100c61303050b400514008030704818540040c058186080c0b403000602d0f030f1110405c0030f03003000c0c02a0f0b20030581c0108041ca5802c04808101c40d90840200242e0727000e000180002801d40c0c090042340c11218100c01c2902d82c0411606042c4c2c80d14505914001499008000c007500c65000403035000e05642c0c9075901c0b9041e07051b00d5034520444200c43c00e0002d40c1991000e0000407401c0d041c2d019885400d11030352091 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 813844064 1250 813842814 813842839
    0x1a011e3b03070906060906031a0d03020c0432042a031101050f040b0319060605130b090a0b1b010501060e190e070318050304080604021504060e0105070311010c0e 71
    0x11000d13034025100d0a4003040c0408400e02000c0e0080d002890140d00100b036148400c914030700016142c020880055015811481c0b04036058100b9000f10b0a001c58824120895100907112300401e04200c20700c01300205641c0d1021030708120581c410f0790501038076000c61000600c2c0b100f6a40c0442503070340c1700480b0b1880728141d5295007035004105586040341c036160402d0a00e8034080c208880360b4802003001700d5a035aa11080d0341ca504051050710050165a542c45403252a00d0581000c46801d98002048488051002c1120340d5204106101520800181c00f6200e0300404400000a45045840c2285508120010030040c1c0d0102100a007a1400ca030305d602896440740c0000e41800c4180100006690100005841c42d030194100e890b4500d400071603110907040c075454141c07c43e00030743c03c2850300e40c10407010711055180400c4600d0007141c60320400c61400d0f140000207461514080d1040d810300c90b0104032082818000e000818001c1401d800030300031101081001440ea014000c212440f07000d0b02c1189 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 813845314 1250 813844064 813844079
    0x7051b01180b0f070801080307060f1b0f02012a0c0503160f030306060309050d08190504150b060a0509190503101d01020702090f060d151a011e3b0307 66
    0xa18120390441c4088c40c50421181c03910400b800140001036001d039250800c1e01008002c0d880d40c036820203043e03a50121401d030090300c02429071320306200c251010f605c140d011290706540030303021080c290042d00b400404442e01d803800318190b0061205c0d2111001d041500081400034000f900441e440c400d80e0100901034448500383c00300c0f4030840c4080e14035400000f003242c0990007003044d00c0e000a441d03240b8000c030b03101042002007510001c54045035141840d080d0380a020031035000385540c20f5003c50740541400c0b92070900030028014400028401e1105022403084007070500424130140c503000c0c2c01d9030309109901007100d02800f00c00401d0302d11340d08186c66a001d541c5041c400c0d20046a030040031403941303466240d40641c50a0000d498150300412000709500000e401c1e050a00070350003070300320229902400b03001e01132000c0c0814240905112000e1210201c2d40205806a8000b42c2d480c100140201c550501a0748400c19208241558490801180520825416140d5000e0360120212505a40c8071100c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 813846564 1250 813845314 813845327
    0x20d180c0602071a03041101211407050406080f13141f0b060d020c1c090602061f0e0a06080115030b0a020906030402090717040c0608090607051b01180b0f07 69
    0x80f01d0139421002d0000c5400102210340d80302c803600d0145014503100907130b0900c1c541241c1c1809407050502d69070380305c924081c10300384214540c0a080c41c10407e0400d4a400070281c0300140007402c40040403260b400203045100020000442c10b500006508194059040103d903200d120200082d400c034a50b24004250480702d0007110704804020781a1401c0010070704440c0081d4000c1c81c00d540d000d0190101d079000c005d040c0344543e40c0300c00043e13941d045414640f030703000381c10024041d0110445080120710440030302000c1c1101c0048030181400482d4941d50b00c4c4101c4002c000d90b80205c2103550820000d1010b0006814800007601c0c061280b1141c4d03500c52102640480c4100b074519a00b10009100050140c9419043e0940c0040141018802d40d15184e0070388005203001c1790102d400f0070b2000c0040c4403180d4400c81c0564005041740081c001801e00150160050003504c2c508e541c01810302145903e050820340249490428545041544c0780e41e9103403001030000d0445200110352000c88c0040d00441c07003000c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 813847814 1250 813846564 813846599
    0x307051c05150609010c08070c0314010506031b0126010f050d0b0a05060a0e100905060108130809060f030f1510080403030b0402091c0201020106080a0213020d180c060207 75
    0x1d0144000c800b000030300c1803a4124160841c1440502a048004528480000c04800c1d10072071688441500710b00d072143e440002805002010381c501001c0200c55280002c4014034020201e42c0d0701c4006c04048012a9901c4180480d00101a41c11401d2410071085039403140c16181c1d51041c01c048162190300f0301582c08a0b202c030241c5001003004c0443c8100d20164002a00b201014104600454440540380e85088050701d2203c41000926130400035290244200f60308101f09182201c194100b0b0049000380f850136410240002c03800080d07580c00c980d981011160068510100d02da1240b514111480c2da20808480c0c1c2900c00702d08040c00d031a00d1034080f00280011802d62070f940d00d1500c45850450080c10984081d9821036401c0110645a40c2e9107014404403140c0c10394011a10347d2248002402d407811540b04202d154081183c05006a8803448001b0304409030340401615208402c00100190800100c14096890303040544014800440300c4007080c2c0700f6076021203210341e6403143c41200058102c0d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 813848920 1106 813847814 813847831
    0x90819200a030b07090b03010305150a0f1a0a0602030a0210020f0d0504050d0e03071505180405010b0d0c1b11040b1c0c0b04050f1201110307051c05 65
    0x180d11409400303c0e000031800c5525541d07272b00e55030314110f103402401c0a481c0700029120b10ba00707030b01464151485601c103004d1042c9041034040f1840c0c404088902800000c0000706e202030001048459600c000c1d4014040601d10307000071002034000303e600380803140d03040110100344e440b54001d1a026500034005080780b842c21210103009030b00c84151a40c001d40042c80208130b040350010030095050600d05200d540c0e2105028002c0c0c4021060128903400707860030002040c1ea06040015000c1d022404da0100700014800304182c580303080007084003551134443d101200000b2018880c1b0b002c2c1d10005400410809a22000204040a82c01c1740e03500344000070024200340000c150754000180030a0b03030440c1c90701381003002042c01341510302000703409808201c0c00e80070440d509500503010032007142072080d180e003442e05004080b540504061441403a00b004004102c0ea05c6104190041c446d0 = true := by decide +kernel

theorem cover : BRFrame.Cov 813669064 813848920 := by
  have h0 := BRFrame.cov_init 813669064
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813669064 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 813669064 ≤ n) (h2 : n < 813848920) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
