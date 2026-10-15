-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5302
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:25:17.492587+00:00
-- url     : https://prove2.me/submissions/36d25406-0e99-40d1-bb1a-3413ee2fd699

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 953417266 ≤ n < 953597122 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 953418516 1250 953417266 953417279
    0x60c0615050919140103020f0108360f03340803150907080402031903090e010f0f090b06040e09030705010c0504090c020c1f02030c0102041e090b030d0e0609040204 72
    0x1a104449190f01c0010001c558a08045298481003408080d41195004131848010b51040c245907601440c6040502400301c40b0340d02d49400288040c08107115100d820034406012402030107641c4104205200452904a40030400120a2000070032404c20b2079005000904010881d105100d10320340c030109280e0b076840c1612071107510421101e05d660280000d8000504214040c031020fa000c0c2d40c00900501c031059428444040126480300704904119204000240100c0c082c44818007074400000a400094141620000f40707600907441804180d0801e6400c2c1460b407280d004131400ea8a400d4000b620319074540b100d0368554030441c00e00070495817074000f4800400d940080540180c803c2040709000402c0c1c544412641c0345040c0c2c82c42e80d0b00c00707007440102036a03180d440012a150310b107038015281000c0741d4680c01030898000f6031190840d04148046901180c0071802e05802400b0081410001c00400c20b0109a9034508002082d007440305944407203000b613540700241c070003880001f8029503a954a034076 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 953419766 1250 953418516 953418541
    0x1209060703060e10030b0903070b15180f01090b012c030c03010c0e0618090702010207050d140a0c051905010615030b130b06071a0f060109060c06150509 67
    0x5554100080c50220b000c5000003001e00c12074014074044010040040c02c54540d84c482e0304024014044920080004000050000c4501c1d485501c60741d850b0540d2031203540901c0450481030246120400103201040340c0c1809401540741074800c0c100300003800d0700d0b40e407005880c210740000340154100d0700700d4400210001f001c1d40742c0d00c40c0c040c140c090310b40392421042031500740c43d03582d50b076040418800000d100441c245800a0640b0010040a04518004210200c1c445590a444080061350002443d0051040800118816030340c58030f041c04240e009200c1c0240395015920211081040103c004004c3c00000c011b0860001c1e072619407444003140c2440c100340204141d20134480c20032030050303114249078041e2180014032a4042c29040c03804507009840002480001d0601c0d41c40301c41400786c1300100c2c941000e140c0d16020000d021512904250816451110008044d14100711aa14044c45017a80c00460603040780c1e0312a0022940c10300d0083d5a070841b2102e50081600251081d0070000c1101065 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 953421016 1250 953419766 953419771
    0x2f0102091503060d0312020d141e010501050405130b06032701020702060906071a0a0903081b0a03020a021c090e070302160b090c090a0c020d021c0311120906 69
    0x44400741844480c0e45503000c01c5000481e081e5501c040c06094540c00f01e80904c01c0912030802d502c03c0140303000340c0140014121525980000c591140d4082000314100f9586154810f40011150340c20240d850000024418842d038040c1034002c008a1340303503030b402e905103030486d800d03003030000700615224905020005181607002c0349030095541c51082e82e480f980c0b4107100b04c030550368001e030145240c00c4081062244c42e40c041a01100c091101c58a690384007100c40a10318024110504085040c0c1c42e1814000c020001c003612810410314414140303445894840c04488101015040260701e43c0101a0b0503402c0c01b4485810181c00c0301c100c2940c03810664840b112005581e0f41402500d044e8507003040881c01ca006024500a1102000c2401d5000c101c0e2581540d42c000e400c1e01c1122403408480d0045401c0c44429540241015100c1c8007071014180c0501911ba0100c1c624402001d002d0324800c0e000140080c012445024966a88134540e84048138074111011540c0c1c00701d40d0081820100c060740c8d5641c904 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 953422266 1250 953421016 953421019
    0x6050c03100e010b0d020a0c08070602070b01061d09071718120a090e0a110c1c02240709080a1b060504030209070f0e03010908070218162f010209 64
    0x91200032031640c500c900c01c50f06031a200000242449911400c00c070003035206504040502680c074035100d0015410710010b00c4210301c40c1c0c0700562103603124034000e00a04e4068201d01d09101560f41d24244900c16694120300721001140c80003220b40310800290341900b080a07090304002c2c440701c10040d449803442d080200d41c6a03003800f11000c528007810a403031507019800008002420304141001001d049890300c642180403050005244a03000006500a034012110302d1000d8010003104c42541c0c03626038640030121140e0000e4084c142c480c0d0500c090104a140724070480c21010000b081d00315100300042006404034038101d4402508504202c1c0c40071815005988040c130302080c0c08030b0450320030029203040300d40c064400d401a85030308a0a5880000c040941410418402c0a468540d542409494016401902d5070b42c3e4a41e51030041c005403070203000e59440c65001d58401d10005a5003140c082c681c80c03099107440c202d480418503003441d0720f4040b500c00d1102c001f810494111504019401010140c00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 953423516 1250 953422266 953422291
    0x7090509060f281524021b0405090a06050f180769031211160e01150906080a0209030118030305010f120807020f0102010906050c03 58
    0x1a403007142c011000d0202c9000e070b1280080c01030b0b071200c40300e280a01400c00c00c6546000c2442c402414410040c0603096210311040d208124082021808585d10400319801c140f001d030012803026800302c0c03011032001c150a4041c03581c0c2d00010fa01080c0a20442c02002d50002050146040c800307603400c0c0030321003030b9070302450140320959180e40b1610002d4048100c0d8510401b0f030704105100c1d02040300481c1c6d07605114030f0000d046d05940c0e0b4004c1907200589000d907480d000010380007640041551071000100031401400c107d8150905c0420720b840c13481c80511b2101d01d403080b076810708103000c1420a03505680d010061000081e0210391030130f00803192810380c1c003a500d00480c3c2080c110001c0300c00910900c26803010600b0100859240d1109400078405008098000300d61030b14844c60007040c9170011902540083c0d5581e00500c0481240d0251000514035420b10300d441c0301c2c15444251051154540080c4661426034840c0c045074000e411254515800c098100110319203500080041ea004490300d80c40c0c180c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 953424766 1250 953423516 953423521
    0x303051b010b0d0209150a08010606030c030905033a020304060e06061e0d050609010b030f071a2a1c0302040617250c060f02161704080709050906 64
    0x1201403085a00881000709510f090026075000d0148220f40a80450b034040f041807076128898698010040040902c4e60000a49030f14200d00241126030503207480d0105820b00c0400c9002c13500001c03d54140e00c0040d0503440108180094015903540040c2074640041e685900d09442c44540794069031245001d96024441070300302c400340d180c59440032030790160301080a00c560000c140461350752040c03003907000c0c061503510011501c55900c0e00304200c40301080c0d6034540c502181541014040d40c412100c242000f0324102e410a142c00b610036081903100c11140c0c1011900c4080801c0e81c42003206081c00003180d56507800e00c1c0d40e0351aa01da118602003607001c40c00303e80803881c00700d02c030b4800c9074102c494603034998410081100852400d0400a0080d00e84285840e4406240e0804907000303214141094450341c240c14168500801a01c51301a003917140544140182850084050b025011096000d040f19510383c081d140324280b10702680e04005414441c0c1600420418071030350000d030003083d0f446d08880701507 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 953426016 1250 953424766 953424817
    0x604082b0b0901141809030c0a050a0c06020d090905070203040b0a1106010e061819050f090d0201051b07031202030705180607020f0d03030209090c0307030e0c0a120303110301030305 80
    0x40c50b04020f450f001009510342c180920080d117101a000700400d03059030b00e00720726000348a00d0075507006c40c280c03102d4201c1040f03c0c08010480b0446c100424140c0050800c043e8148e2010b48003680901c1094003580d181d0700061004e07807092088902070401d070031016440703201d04400103000221008a50450f0302c5688004200204000d0702240b20b11002040d503c0e90b550020300c203601101c000351520910505480007403500400b103005641c8160b02a2202803180d1400040c401e140c0b0b8041c3e040f03202964940b109210008030000207080034000040d501c0c1e603441c0c030306150031500f0001104c112004d441c408824024941c0c1d0040c01080203a1001c008501400728050070004c20303204080c802580028145144652800c10310b005603ca540a810014204100400400c14201c401c5031500d81c0c00d4400020401181e404d4440d48408545000041895800030700200d102812036026030891009240c14050403d8800c3e00910158000c0b07500c01a12940c0d42d16010301603410040b54072040c1e88286003804400d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 953427266 1250 953426016 953426039
    0x10303030f0e0318030312010306140a020708270d03021b0a180b0d061a04140601080612160b1812030406050f040e16021e0604082b0b0901 61
    0x380761032040075610300302100130100c0d89903482244640c0c05000c140721095580b0f03070f086801c50003076004003030201d6810308a28880c68041d5000703001e40312075481030004501251043c0280d800c12001c141d00f014180c111140d407011254040b407142c5d41d00039100d8403440201607001c100300210840740c0c15291501e49100c0d0400c0420400c2e40140c80c8080d64040e0401000ca10540003c0c0b002c0c0e0002c0c0c160026400f058a80ca002d4541803440007142c4010540c4104081c10b207440344a101c0340c0e890343c0d26080341c00c003100000c2600c0c0d4080c10315441041c00d00c10300c201c2e000007482140c40c85e2400c1460358101342d550b1184600b4541014840c0b40d86054000c0381412941040c1e41d5148044030b040e8051498642428410b5595411001009005036024000458031410712410203000750a590307522201050b52800080c5840084110b520468501e8080c10500d841c001036103a030043c0d4821132840d01c1e44e6101b48000c0b00d08a5107528161000d5000440035915201640003803041c4174180d40043c0585e0f210282201d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 953428516 1250 953427266 953427281
    0xb0c100c0c080d1a0a030308040308060a0b0703031d01090609020f01110d120204030b07051e13050103090213110a08070509130903022a04050108070b0a05130b0d05010303030f 77
    0x880481005207000c841c0066001d81c203201080d00440d00003403107800c0800c01740c11043c1c00460100742d00d08203120038141c00910941e40440101c4062128508081e91700c1418014403c0041c24140c6510702441d03001260781179141402d0360034000b00459030040c03c005014041d2a9400d81c000d00304040c40506552103190021000c1c41414001c146880078000200d4140720404221604a0f900740310200000c1c1c501c04070103001d40043e507a02c680382c0312400c0251b00040240180410407480c100a40c0c0d100740946c00c0e280c82102d1003400c000581401e2400490340740f200e80003010b804e00b45840c0c00580d48074031103400351030b4054071031761340c0306003581c900340150f074244900d040d05503020701808026103940b1002e4102d0710b00e07103210b4410b5482100e003400c036241c1d08030300204213200d040c500030324448510b0525126032801840907800500e102d52400c04040d216118905a0508000c000240481005105507613403000785100e0712002d60b6078240719506801080280001c500080c00d103900110590b40a009058 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 953429766 1250 953428516 953428523
    0x3084209060109030b1504090803060306090c1003021c050c040305061f030b060105130602031e03010e06040e150108010c260106050a0908060405030d0e03030403140304020a0b0c100c0c 81
    0xc3c40e5038250b884085940f41c2c0108440e0300d90b08000301000154880f4042c03204c1e0588a10b011a8507410518101410301d1001813490190740d015076070040043c4d694030981c0c400322002d410700580da003c910360001159030318014500882d03810803003800f80c00107208008100f1280134000391180d6445000b030150b40c035040a902064203400b169414004a801901281e80140d0141401841e00e225204102d004141e241d03c034030b01507000404d9140d003500054140c2c003608040305070150314540c10b29546213030a10015001501556681c07120803c0400304005840c0d1200b50380c10041640d60b981c03103c6a010f040101d00310300016166202c400c1c51101d070960026241022220309104580c02d04800311520f0304050307250030800c00c82c41c000140d241402d01c4000c1c0030381d020300d025507039420303c42c00b0201c280c40c4c21622200b91540100200008071b58010001d04805000448550380d90300d032800010045c3c000e075003060480a41c00103940391f413100006411505214010024012100000ba06aa0548560b035018 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 953431016 1250 953429766 953429777
    0x5070e0f0c09010e100206011410170c040e161701030515041e0b0412111903020307060c0c02041526190302030d0f06060903030842090601 61
    0x122100710000180c42019418540440650044c50010f00b410302151041c00250300018010300c801200b1203017105584005a82e24048a1100c450041805240109c010b451480842c08644041c42400c12600286184a0440e07200e06041c00011400d46040003d0004207d00040d0f4181c103c21f170282a6040302d401c8005441d074200d160090184034000180210b500240d83c40341c99100e864500c0907810000e000300b00110075480d041c58803171306c101803241c00b14003844201102d0346003100c0f0004e61004003c1000c082c6070012070041c601a0302d140030701c0f00c0041c40541058035000e040307640a2004050a4000c840c284a441540d400c07110145106000d034180442e45031821003410624085e080010540034022215418810080c5543d00302d5030900440042c1c10019006110725524054410700c0c02c442c0404002251400c4400b034001305013840010705000f00000000c280c28001d079005070308440c2400403544036020420300c0056408021030141000030310388038250807034184400308602c2840180c442 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 953432266 1250 953431016 953431021
    0x1d010c0b0a060302040515030f07030c0501180f060507030f030605060306312c03040302120102130b0a1103090a030605060a150804030f020f100506240705070e0f 71
    0x5800038490020801e1030320701d840b00000001a105c501c10b241c41104603001c101256260201098103245081c40302010383c1d400700e0030502c045150807400c0c0301241c009082c000c9011990a8498215031b0580d40483d8444204110014002d0303004001130101074032aa480c000302500b070300d0080d000c0301c1c40340c0502c503004602070002420a0904e55107010040003905401602c070080c2c9040215510b4246502d10b03d15a01c40d1b81c1403440080c404c504c40360b005170101e070000d100c0b1400c20110355280a94440a48602c05036501c03104007100c00e5044881e8102c0c020b0982d590581c030b031491101c0ca640400b10500c00503c00000c48140c1130301c04010303501c1d500b5000340350340750140c0703552150800f405000e032655510a030780350340000d0911a400c9001000c44520303202c40b8102d180c542805020030304130080c08825900079020340034a0a401083c101411164020005125211540442e41d100c4c64402481031403142440d6080a0103140380141900c03d00c90022a80d11503158541d940c0c40311029108207120700040c101 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 953433516 1250 953432266 953432273
    0x121b01030b1c06060608181923071703040f03123b0108041119050315010305071208070803040302010b0603011502060903131e050409121d010c 63
    0x1401c1c141001002031203505440a000c900606402c0001c80c0d8842c0e88000030858950070010303442e4085403143c003442c0e01445890306241c65006081a05240044c0d542014082020801003242090002c1e80203803a140d81400019650b80310b2402041c03500c851011070130385c041030000112400da81c3ea02d28015240380c5150b5941c203000c079200d1a01170620480000391446601121200400c0d41d09002880d44402241c000c0c00101135003500650b030410503100c0801001c107240c000b0703a043c1c00c0400d1b41c2d500000c4030107411080f41600140c010580c1401115071110b4000c0e8a100583e040c3c9014030140c8210654904094084004012004110803000d00c845000f050450019552243c02070001107540c0100d04000b0f41a039201741c0003c40602c510a0400c0c14041e410060203a008041800551900c60602e11041004045205d400070041d0b1048042c0959420003e0101c01007002820902c408005443d084102e030b12a0f10200000a90700441c80c24402140384000700d1881060b1a1648603107840e44 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 953434766 1250 953433516 953433521
    0x2040f0213030b0a0207350f03040f020d0209190501080a03020d0c08160c1503050c1605011b020105070206160804061814031e07080301050409020d14010506121b0103 73
    0xc00004000b61700380844408a003100c180d03001a0200c000640c0c0d0a0344c0038801c40c1e0035055a00280a020703070030a11000c0d07039880116013102e81243e001289240402c030684002141c884004400a400c0070b104010300205c203184004d020070000d41620306001d540e803125552035880701c20020140040e8031804400c10079601410b180754810b0300840304246824112226601da41076641c0301120b800c0d11000301044040702c041100410b24003145018002400c014009021601070b805150100f0898028800d0070083d0075031140661a25018107188150070200b0043e0080808850010160089900050003022603c442243c02d40e03480d02c6004040d00d454030748400810208074061b034190310520101e004100000050301c3c06a8041d0001e40c2d6400c40c5031244802031242a00b0015030040610003000090070402c1641d05441080d41d000500488500000f095000800005001140c2a28400d10382d031206400c410721070507068424600310b9a217011041e0340c46240803c0c47d03242181081100c10113610a4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 953436016 1250 953434766 953434771
    0x2030a05031c02130302120a050a050a03110d0e0f04021201180c0203040312031d19030306060e1e0301090803090705100c11041104090e010e01050c0c0601030f06180f02040f0213030b 80
    0x1007048234012242d6680c1e0525241d20050290340e10303803001c603c0034109984900301d40300002c0c801d00074103440050b021002d00f00009111400e0301c280100c0300c0c000c0c8079456a6042d274071300300b04034034500d119540c1d41c08800d02072010344400078005038104040710007910700010071581203990003201c0b039141e118202d00440003045064103442c0b828501d4180d01c41124010403c604019000040721214402c0702d03d4050100c1e00c8035031040091240c03002035210150b440d1081e00410002c0d0341081510f1905100c0007034010804d040000b08050404030038003d6841000400c2c000f07594003503590360443d0100d0401520441041c1ca001030484050180d4924941401d0700165440d0f030800c003201e0b00f00740c1c0784d02d6090251901070700c0c81348443c0c0d500d810111401070709000d0319030807942001109207480c044031800307505e406050101a01040714280070340104030701c0764400a040c0c82e00d901500b5000c2501d00e801e40c4406400303a4247d22807424010018044047c91080322100381c400707007180700300c540f0310b91300c611185100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 953437266 1250 953436016 953436049
    0x702010512040816110405100b0a030e210a0e0103022b0b04020f0a020105010b0f0a0f0909091a24132309070609061d03010902030a05031c02130302 65
    0x20301510b84028070401400d144c084c89144d01d40c0500c502c240600c01200c00013002689910880c8800b040002c5424003120001c1005140100d20b401d00080c106107804020301d183c83d6183c5030300346030100c07016440300074051000280c3e50358021a500003004509a005e40b0042c004024064007a181c44512201114020540b0403040441c005031160001012030304031b1071500c4c250000000d8031000713895080c41024003400082802d6030404410704012501400780c00c9008040c04080d0741c03d1a500b5018040c054018400c82e0b4051000c5203030761a200301c2129108143d800019030000c040b0f45a02d02c2114448214511214807130070580e00f01c0b0410000c841100c003840d41140c0c1d1a0454801c42041201359540c26003400d000d002d290415120540c50807885074488010070008010601c00ca5510001020865002d203030402c10900601c40000d00404450400030740c944180b00d440020440048050150040c00c030140710081443c00f606101a4032800d601c440c88400402801e100518052040d604031910 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 953438516 1250 953437266 953437283
    0x31d1c1701091a0301050c0316020a0b0a0e0f0d0309140c01020a083402010e101e050c061e090a150203040c170601080d050406080f1f090e010b0303070201051204 71
    0x3502c5000c0b078211b070030940d01e540c0010b100004010890321102680c00e120380d140d1004142820072600e80c0d8160940c050a0070380314030346892413608a0241048074401c040b1551040e240c0302c40c01c00313101400800007408200d030880001c120b0807600c1c44000c1138245242006030042d1049801c5541c600c04907070321107020742400c006401c1381001e44000c40c1184802d100210b859210462055000140c80e00e69401501032051402c000c12a076115441000382d014070902202c580d10701907100030306a1311409561f00c404c08a200b50020070110080c0c01000a040c6041c0c41c1004031951100c0e12610340b07540780c10341b0140145010300d103403040c204c4803903000b107902c6401800280c0c00c84e505d42c0948030705c2030480320741405250f00c0040184142d810a0048008030804d80c10903e140c90701c0d0050240584100400b11031400301c0100001d9140320f003201c80e450f440d05c40908000d010f181c0fa2401c0500a004440c500c50082d840e1001143c007900f000003c40783c4554058680303e091036504182502e484070000c1088a2914 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 953439766 1250 953438516 953438561
    0x2212120309030c12181404050a090f0803130f05010507090e0915100b0417070504200a140c1615020c090406060801140a0e01060b0406050901031d1c170109 68
    0x200e0905c05800580721a01030382c10303841040c0341044140c540150618040500e01f030300100016a1070080c0900d1603511400d140c1c0c9958596000c200c1082c00108040c2207a0030940502c403c0000662005106800d0f6445000d00107031200b880141300e00e0116140403e661120245480b0005d07040059603208a03a44013042d101d075100d070342d400c00540082c1d01c07010204040e2410310340d440074180006009080191420041c0d150301142000d81d0b041c4080010f02071709000580012541e10510800285000009080743d42d07135800310291781d0f0358a011012540c207a50450010801610108484600000030750003014240d807084100706100c2d0025208444e003c1d078a010006113614280650562032131516004a00c41c500900100c013580c84841000d45141d24101050141d00040307015981a6500da203800ca40b44c0c5490710059000345101201349070b03000d550070b030f528031184400030754038008410742c00d0329000c0402c0c070b40001d40e000a9580340c17480b922048907006012250081e40706101042010144140c2070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 953441016 1250 953439766 953439797
    0x1d0114130e15100803070c2106060e01090e010207080702010e0d05070b0301140f03210d0501121205070c050f1807020604120e09010b2212120309030c12 67
    0x2072a4450500ca84860305410088035009440c0f0000041c800304001d507152003002d0750b580030b40300e8083c010703145540c0740d00701c075846140d42c8007a0460003d0760010741042072640324952000040d800b44203802140b41000ca440398a001c048c000c0d90f026a81c040f40742030800c1717240ea0040d55080030344070403250408000f10030071011844c2044804018884245801e5407941003034a4608165402064140580d54183c00703100d40307031030000b003c003800034910401c8945400e070f07a404102d1500c110784108024a003010004182054103c0842c1c07003441c0700700c0d004001e140319003800f40c4007401940400b070860307040400200810304001c03807040c1070b601008020700d5091505800303149441c501620a1801030740210100f0040000d601902c518906240c201010b480880070001504041c05000700d094500020a01090080a000502c41784455041e26640d9158855002d0a00340c1c0001030251100030401d1200000c2502900c01c0c103a504c1d41503918034268061540780c8000c00c145441809040000e02d9803500307281d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 953442266 1250 953441016 953441023
    0x6010e010c021e06120a0b090c0304110301061703120a05010e01060e010302070606150206060103060b0f0c070302030d0f03180c030b070c051606020f1216051006030c1d0114130e 78
    0x420b501180000c01c0781006e9034010201c0d142800e0060080c60003800381321f200c0d0f8400d4243e0780e009601074003680c2d04000036400300340500010b43c00f2000603801d0b40000500d20784003001800311000c403629080c00d580c0d036101d0b08606446080c490315601040d08001440b1080c450075000701710600604015241c0107099503103900b100d2a5601800c9c3d5032104511105c00280d06000544e003001003440c06000343d50030906c50130703803610800480e5000414006813410f0381760010b00002e00115002410750304d81e000340743e0380a003c0f20600d900c3d00c00041d1410101a200030400d900d244d0000d0740203906603041c07904668031415020805068a030512900c001c1401c0003070820804248910b0100d0300d0920303401c2c50918045e180c1301c0725450240071a0080e40c82c2c044114100341c2950401c7c0d10070b244148005025081c80c50800c850502035000c61741c00c002010051010340c0001004a8a08009140b030380d0000d8a094100b854080c026610109030610380300849103420382c0b150300c0c40c040c0e44600207150310b0300d081c147c0c0c903 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 953443516 1250 953442266 953442277
    0x71403100e040b37091b060201020a120c05070227010602100e070305060f04080f2d1c1505040207050c0102010e061303030911120a060506010e010c021e06 68
    0x6802220781c3c204502d100c402c4280705107410022442031810b895520380c480403100d60002e424130503551401c0c100d050241d030504019441481840f1008070544401c0000c1c0070f5800300340c1c8000403800b4162000602c059a04c03c22846403034035604c690610030a40d00300400707650358510040f03060b442e0721040c012803201506d00764000d11007030b0002d0081e010070010900075512411040c1d29503810070401080425004500036502c506150081d030210382e12403420840c0c038002c400f02d0401e811000302d0301c1e0010803840d071440451541e503188114090300021821590500c03580b224401e4045074662548500c104582114030020341c0b403940200441c0c1c803074010500700d0304000010380f0140e000600000715960207101c2c810201404402034611881c1c04001181e001850440003410107503100c5e110024004040d54001c403a5030700414103103040061903000c5607a2102e02000780e03040303864072001c51219809441a1400b003030041e191702013409419005c016141c14a070404031590030100140c6805a0341e060b00404 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 953444766 1250 953443516 953443523
    0x10c05071e0b1b160509040209130b040b01060210091a0601030b100e040609020406050f030c07020406080a050607030216030e0604030602160605060f0d1e0b270105071403100e04 78
    0x84900b003c0c2d20580d29060346881914241003000c8000c0c0f2803a201c070004154442d070150b03100c1e482c545414111951a140d07090004d410a10301c3c00c07e0004009000a07d1812225140d084a651000b03102081c0708407034234060000c109000d40d001d0029001110100903622000c14100021041400c4002c138001460442281c0c0c0000d00403010a007151400303100f010050107400500310b00342810420b0103003c41c0700300442c5017800710010001928187e000341c22200032603130142c000e020701030b80c44103015625241000101c1d110b0164070000b4501910a00c00d1380d0080070000b80c5c040712440551015078079090b4512026810400401012001c2007860000b400070900120415202070342d2401c02c2421076001800040c480c400b000c601918954850840104098010150400072500e46032080e503040014400100001304042c00c1080c070401c041481c1007050010950840b009610b483d211703003255001c40b00d000104920101c02180903142502641c0c0c4002c40f03400400d11262588960040c03060225004c5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 953446016 1250 953444766 953444797
    0x40e01150b09010203041206020c16060201180309050f0d1b05130204183903060501020f0709020f040b07120e0910153b010c05071e0b 59
    0x280d2500c4404060000102a148003071400c000310600000d460384214414104a50351024500342804040d5045540c02120f040480d41c4498607085810907007015407013100d01551038a02034092006291503511035807681590f4541200d414075040000012008848607001900040705070001900e68403c1c80e02401c0b50000c28607003515013001c1003603080000003c0d56415006100c1004074640700c80d903070840078180c05008503e100c01e44066070107042034000c2150700609264000e4039084241034514401207450350b82884466102c10040ea940c4504180001d000d030b101c030108004400055005c0d040c0b403138991410900d001e030303500300100d00e540001f01c0071344190034168103802c041600f100c50100c280005803910f2020340b60800b040c41c03286449100c5e9080c007440c4241202030243c0b0580300c0c00d840b500f126036941d25021404e001915101e50b6890302d181000c160580c1285290700401c4181d40d404d621200501e00e03241080d2048000404014290003140810a008140803c0b08006844c0000300e51011 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 953447266 1250 953446016 953446031
    0x2030c010f06050a0f0b091e060d0b150a0c11010302070f0b1009111801210902040506030a05030712090b0301062304060f080c071403340b15040e01 65
    0x810014000395030010700c084440403403c001c0785401d1030540d41c0c51f040071518280c000ca2645809207143c40004142a40311400184810300980d00364004511503905503225032102040603081c00c01446031010b20303c04911411103820005000c0c10300c91080d85c00c1031402508150080c0c0d5800307000501640e044504190310000c1281c1601c1c1d62946a00400000e80d05007c50f001d5410042c01074030558820104c10782c41d00340303c4001130340035840820710701010301040d14441c451070303014070020f110341c0750101e11807810200800e100f0f10340003414181c1507800c90301a43c0751104586c0c1d0300b403a84226038001800e021480344001208082880654020aa075440e454295080809030a029a90384450410034040c2800240b00ca41d500009580300c030f1210742030045c50b903102c2c040c840003507004151005183d1801c04c4450303070308450080054800b41c04600c1a41c2070903c155040340c00411350003000c54407502c0380280c2d624045289984c60a80001d8000705204140070f0280108081ea0005842a46032769100c2c20b8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 953448516 1250 953447266 953447269
    0x15020f040e16052502120f16050a030b0621010f0e151b1b010f1e0c0512060d0b0403020c10020a3c050c0f0105090901031202030c010f0605 61
    0x2e03150750003410352501074542030315031408460030ba02800544d0700815004424208546a4100c804e2080d14440c080302c02420003a40d4241d6501043d01e014081120090705c002100c0c2818420001034a038401d402d500c0075078943c2c0c180154991031072502e1884580c2c00300c030075200d05000e120b03513007110042c03d00205081500c030941600e021702042941200380703542410024408000c041c0a2a441e4a0f190300c65911a45001c05082d0341d51030404010255180583c2d403490205294002c29668001114149901c0e8042ca8094121051503000c500410010005003407c0700b02541955404400104503d0718001035440340d9013500c0e01110304a0143e400b08040c0300391f610b00840203103d0054030380700802c03460307807143d861180d035105800750807150300f9031144148804107070350940d01c0076100000f52009401241d4107060380c1d1100c40002160080d901200100f405500ca07804580700c101025083d42c146920790303031710741011600503440401140004d000e40c0824003028001c02140041c96940442e80505210 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 953449766 1250 953448516 953448541
    0x120408070e0105030d02100b0102070302190e0906130611040902160c0909031e0c0b04080a12060510210216020301050601050c06070f2f10110715020f040e 68
    0x82043c1c2c8658010a509008180d00141c0301000000000f40807078014000d000503458800d054000031351100b0305040c00d81081141180c98402c5581402000c6129120343e60350701d0710344006841c2043d0074216000c2c95000304480e50031181c2d0a40c070542105240c01d0766410f083c0c040fa001041c1040b40d1001c80e0913007a090150010410020f00405103041040c5400e075940504a401402c0484079008094040349903200c3c000c102c44024150040780c81c01c81883c051070101746503407168004101264142c1e0841300c040095209200541e14042c003120712400c0c8079001600c40142d4407a85c50741103150040e000110317014600103480c0e00841e41991804441d420f10416094400040c21181000000d100c13104810400040703a58002c4060b081c00f00710354084000490b4401d40040800c0c102c0d01c11440310b107246004d0040c408a9041d003010603030b00149403065508003038905a07a1481c0c510802409240003081070002c102013803500c4150b005140585141c0c203c40303240c015034043e06d01c10200800300420304036200c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 953451016 1250 953449766 953449769
    0x1b2704050c040c0905150f041205071e0504150510030902090f1b0d0e011e0c0c0822030507060203090a0608060a09180203061006120501080c040e120408070e01 70
    0x1242e09004400c02098020300409a0740319261180e40b120105400c24100c59044684110094900c0c90383c0302c0d2180341d01c010190360200c04035001c0c8250704000548207408850314101504640c0c0740c0b11514648400c01000c0c080080d80d0010708030062034001070f03954940500e20306181540d140450b02e4610750042044c220001098a905842c100c400c00c030814240780c500f00001490050042d07201d41c2400020350041084001090441d86001c0d5000415030b4001210b0500c55130400003444544d26403041140d107500300340e01c01856900f0a000248402402c00c0e1080a901c010030364000d0296a030341c03207840c40c0c0201540710102503000003a2600340e902302084004042c5c00c1e2401d207400d07541001c0c404261600c409108104410745e840c5580542c021341003480c83c80841e0001c0481c0c0c3c031810701840303178140700701d05201d18004102c5180c400380d00034686005040c100c0d6030200c080e00c452803404040c40b01800d441c04582c8140d000e0030049003001c05440010340003030800d80c0010200c0350b05044d005813145006 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 953452266 1250 953451016 953451019
    0x406271814060a0501140708030705040509010b091e031915050c070c050907050706050a0507110d081b040b0a05032d0417040503010f020c1603051b2704050c 69
    0x80420000903443c2c040c9840201c0b0003e20b00205030760b81801c0d03081294056210011300c2140004140036034140e0250150050310300c116084007081e680c1d8294188980302c1c500041760400e2442d90030403446802c14940520481016098403411040e040d0203259807d4510001c640c4011000382211108d6824440c2c0c035400703600d84030064501405915071302150400d9100d810302c10900040080d03600c0e44100142e03004554045070034007150810007886030180c07404588520002c0c1001c5800780440d400018190011140d072740765500c103504e56203580400c030f40c24000c0c0300c016860100700024051148000921b034031b558a41e19079499040a5110040391203c401400082500e0107010103600c250320918243c00981c020310714003a0840d444901c0ca40381c09030360300050b419440d000d9021062000364005280010b001000d82f0392418040001da007020b102400003800d1940030f8021541e0800601c0080c00e90104020800c0c1c001344404a5501040488a54440e40d40c200a006110402401304000001c4480 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 953453516 1250 953452266 953452301
    0x15180318050f1503070302090a15121e020304080f0304081215060307111c0921050c090a091b06020f120a1b050604082d04062718 57
    0x82c5440020243c0c03039035654a01003840c0c0000410002800381c1e0480c2c01c1c00401070602410a6500c80e041b40d039055580d40003401143d0300384414021000c0901c981100c0741105054612021402c540040c000d41000b001220026030030008640d081c00d4040142d44911700c0383c0344160740d0300030a80c809400a04068208036465001001d4400941d4900d415a40e010b6028684580144a002c0040349881d60f000f0410314461038068488140651210000054602c0d0038102c201ca00d80c00205c0d0001501000009040e58015035465042854200006074000004410221301c416090700c640c840c0455018204030155500c04080042e96010301c040140140807030040c100d0140030000ca030250b841990700c0b803010801e4841c3d49910000c040e0601503900d507000000c880e03c500d0103213402400781e80000c61400101c03203115100716204401c0d0031100400c140711781d101d6081c24602502507d20f01600c1d40b890a0050520b0022042c4018500f40380c00106900b2003103000b01d0410745451b2045a0700741801c1c03201b021 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 953454766 1250 953453516 953453539
    0x2202060408070e042618041e0f0b0f0a090b0d1415060f18130807151b0203040b1806070308060103050c040608060d0f08030708100905060d1518031805 66
    0x39004419100030307016003100643c6c821450f000081c02404102c00300b210182a100b0151412502a84984040500c0507000c01c000c1c8002403c028001c200560102d60001c514401803003c004240c100210018018040e00c07400c03c2d856655012a44134086c80076507a80c0004170804100102c4400030380c100d0019200d42140702d0108002c5580610305078440b02d00c0f02c3c0000c000c40e03a2000140110b40b580ea42200f95582c480810b89030004685d41003891002c0f0f91f9080540c1d80d40d404001110180302800b41e50003c0d494180780c8840d413640340d000340544180b94004942048441d0302e9140007014050f100b43e82d00071840c0b0303181c0c0c00941218005080405c050200b03100601c85180c2001583c0e400190031114890800100e2030480400720702948014003001001c4144181d5a410140190240c828500e01c05942929008004203e440407140b079a40011000301410200b15029800350a0840402000c0354114002100140315001030340101c00191000000040064515850001030001110702c222040b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 953456016 1250 953454766 953454833
    0x140724121404060504020319141507050307120b040912120510050103020c1216030807021f091b080705010e180601080a1b0507050d082202060408070e04 67
    0x140e500400c001e00d401c0c2e9130303000b107419994200440040f115400180d60340c1c40303101c2c0c540381c110107945d103529501620503503000d905d03648465031000340f02d03185540d20b07241160f680520407a1400d000c40c041200d038542e5080c0710300766511035004038100b080c003956400c82140d1100000070101810f901e0500d038042e00c0d000a110030800e40d042040200c80c1e09103400b68517074035004480c6040c00d4805400030110a00040d280c44401c00c0034003500710180c0030780c64441495175004d070103030384400c03100c03c07a480200c2c1e004031701150f00340d1158001c0d446140201c3c9100c0d000740c5407094501c14030680343c00c084c241c0d6115075020000c03981d006803002c11052090b01c2260b400d00b5106140c81480c0c00140009044c05500400131fa01c02d45958482002650301c8210501910440c190141103588079030300640340c60061a9000c0394250091071b1481c040c3c0750060000d50544a403c0032052450a402c000702d07403002c1c080100180001080081d030000d03012080030880c440c00c2a10f05507428074242c60020341c0700d688030b0b8524141c8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 953457266 1250 953456016 953456051
    0xf0201111e04090e0604051e0d11030d06031113110306040903050d2a0806030a03110a0b090607090f080c220504030c0c0f0e0414072412 60
    0x40c408108900c07815150001401c080c68011034003c41000d500c0d00a141d000001c00162480c00740e400303101503c5070222440500342010107412903c501660041b0141c0c9402c1e0f10407926131600400d600f003a6410f20010644400681c0d0b480c2d4810348100507400440308003450403000f94060345080714010040154182440c05107404003c00d1144075a40c1d0b0101c00050500400480744615030141e4204412000102c40440e2030220848011903c9501c500c040c0c081401840c689001740d00080c001c100c0c0d040d5076601140c0003034000310021349500480a5000004152120743e43c0540c800101501c054502148001c0c90502e481d80440341049200004004803200840c205000c03080c00d8510b120030b480c0c02c541070f44620740c5405c0391005043c600f404100c00d05134002d10110040f807081313840d6041c483e960481904040362601564841707003d048042000203000104000c440103d0300c0548500b580c3c1c682b548201c49950201010401207401d0100112541c440005105880f103e08200007200300c3c5030030400c2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 953458516 1250 953457266 953457277
    0x917070303020709110910020d030b010c051902040b04060306091106040e01060807021c0c11090108032a0105040308010f0e010b0708132c0c0903060f040f0f0f030f020111 75
    0x2130659842c0601d081200242c01101c0003100090401c1070003082c000710007540c0c7c3d0700038128100024038100c5d040340203600c108a8100710540040090054029040b07004511210b1180200da01583e29101c010454480740913a10046003e08400901c01c01a0705058940520041c2e445104031020130050224104201c081c81c155481460b0100641c0c1d80c980c2c050b40703891604030f098422003110700d0f460320800e07602c44001140503108258640d1b01e60f0080c002d01014120070300451800307420034041c400517451901d1603981c100840050001c05040454091400c5840603901580029214401400f0300350b030448168004082d058041400d030344c5041e030b82110340e000d52100248440d000042085003800e0200c3d650004d080e0212207155000001c0c03480e0105142100b5070545071089000000305820a848252100402c000d0041e00d0b42e540e07600341c0d40c1e5001d04003d00c21241000c04003403410214070303e08421071016100e01200f11004141d1304020b070040702000d00c080116810050213950080c2c10009855 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 953459766 1250 953458516 953458529
    0xa08010209030a170d06090218010e0a09020a0e1207080f0c0d020111031905090328030c020303130305060a05010e040f080a1211090a0807030305040302060a0903021009170703030207 80
    0x2141c042105080d0b800d501c551750142190500b810b402080c2c4128541c01049510036089007680c80d01070400c0103464181200d8801c51340f142075150200880c802a030010102802c4520700013092004a0001440b445805083c01509521032071050000c800104070040907103010000a0442c1040350000a136516510f100081c104a414514103501d44001c00c02d03a6445404201c016104409002004005070001502d0910a1187c03111014070011000700c1000900c0d205803214021089039102990601c44002e001c0780c02d84010401000cc080500313180c400514420800f404103414035040c150306030388060b000b0400c102c84030018000000e20040c00d4644035580074299540741c032002d000035102020398000c2c0340c403000e007890b40c0218400400c8009180012049520305600340d15000c4480da103141902008001c510108010300161410360043c0000540c02d151a038519916940868462407100440e2804190015010b01c14000160140141943c0f4080240612880e544000350307282c5140c411030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 953461016 1250 953459766 953459783
    0xf0f070f0e04020c1516230c0a0305030a1407120507030e0106170d03060b2b061d0108010516030e0c09070807081005130b0d0b090102090a08010209030a 67
    0x10003101c1c040d50350411a104020811510742154a070b866807200712008407203030060301c0c020000710042c0c0005120000001503540e0807040100b0382e0626109500f0528109030581070500901c002031104000755482c0300c2c030039580e05440b414055000820386080350500152000307080200201d055100341aa07038280320800c00840c803500d408500b50000e250081c1e0341002d950820501007021039007007005000d00c1024400311b0740340d11000d84084088451354003d004502130108a081c640c078000c10880f100080010310341084a69903145220111009640300d010001d140d00c603a07000810108814a0041c6048002400b47d07160200014284039003a4048009041e0781c3c0101d90008102086101c5c110348010b13021101c40c1c10201006410321000f101d01c07800045404000940c01c50203610204101e80018200110b05580e20004002400c020304080d40c200c00c072440008041004019044e006030f0360400010394071500c01040c040d00c140aa04802610b0f8010080c00d100c0381c4001a10524064101c00300 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 953462266 1250 953461016 953461037
    0x90307080706091104110403050c0652030314060f130204090e03120702010c0c020909160603060503070918020603060a08030703051225030e030702130e060f0f07 71
    0x407149039001c500107800506c0e09210f501d980c05690010300949009000b110100306110003000194072031503000c0d0114880704803c3c00c500c2c0c040441e803c0009034a800c0c003504030381815102c1c207001e060446900c1800d204a83c008505258040c031402140f02e40101c02e04500d8074064004c581d4241083c4003c5000301c140351403014582d103055050f507000d0300d200350342404481f0282c5011070307494010321030850b01e106216012a04841c01403103601c50a51030b40c1c844400307001d465000c100500c0f0b001003500e5414041e0218990141d021109100041c0c030150714000340d00d0703083c0f200b41031034001c81780c1081402c18a441c80400c01310039101c2d290700a641e41210990359917928900451130001d01d41e4007042e0948004503007c0201a00b00014015014101c000e90b12240d650304120a504050001503201500d001981a22030920076041248070301035010460f4a04211a80030601720015800c6440d0640d643d42031a4a0650382845641c0d00100e007001c00c1c1c1e016082c421b040d41e0a046002d8080c07414407001c0c064 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 953463516 1250 953462266 953462273
    0x11030702130501030318030b0402010f050405030105090a1b050607080901050403021905030c0105032203140703050403061d0d0503090c0604080606090c1323040207140609030708070609 81
    0x21a1001540544880d0044801c80158005801e00380001c0700030440d400c040c01d44c0d41c0540a601d000b200c0e0008038940b200d4071a5001960080705401d41241002030412000c603403501c00740a0383e4082c0d00014000c0c60303243c440d400c1007854011002c20488a02250080400040e903440e0150f506942c0c0006490381e5030810301005031b400e4071460344003e41041501010003140e041100c0000c0454100b9801d80701020b035040011109440100c8443c0c0408564212200c65400fa8241d50141c3d9032007402c082e142c40728403071170303401094108410403000a44000b070f007402044881d003e141200e0b2400301140c1e00807155041029100d84007035108108012020000030f00c0c42d08204864010004041c0003140e440d40c07203030343c01500c030700c02203448600848491001c2046000e01c41c0031110318001c8035070149100d600b046031400014034882080b080c400340740006554169514030081c1388152154941c2c00c01e04150411503400c0c0140103095080d550014070403a00812445c4044810b00380e40460b002444100c5807a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 953464766 1250 953463516 953463523
    0x109030305131502100609020a05040b0903010b06192316080904051503010c0e0603060d08090411030f01080705010203030f0a09140d030f0e071401110105161103031611 74
    0x107014000400b201e0b01c881d680f407030300841ea01280802901081c88400d8072683c114007648181404c040004400300400c2141d503080300c1c050215104006c00115541c064000007588580148030850102132084020b040503981000c00c03240520740300c07200a650a0317811107003207000b405440c0c80030b0309244050641008005400c0210381050700020000c00150900300c458100008480d094540658a80842c074142c07240030744414000104000e01140c40d5544100034010070680596045807420b5003802003040303a070b48030701841854003100c868036612407030b0101950b01c176514180e0021000d90040182844141d90103c1241c0c1d00a44034050317984a038440424003001041d025034064041407000c00309203001c5001248a2540481659042c003000d03a0300d1348400d08075503000c0000940c030340c0101d03c00c004400c41280036003108a0141400380c0d00c00107041125003522011034819942100e013101e48008241c0258905103d41e41020080d8194503200d00710141031100e0184800c04c0c4841c080c4028950340081 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 953466016 1250 953464766 953464769
    0xa0503060a0e1014040c0b03060d022211070203190f021e13060e09010b030c2403041121060403080919030e031b0904060207020a091d06060f010903030513 68
    0xa542c1006039104460b0000004130042d5130403601c0d24403142c00020301601d0401507034040c0304001e08800c0c040c040380d420056444000b0000d41800c0c481c2d01011550f00001d8458240c50440c0300c120320f66580170a204041c2442d540107060310285d0300c085c040c2d00208821040031901550305540c600c4641d001400000000c1600100003580180c19980501200340c01c0e030000c80484188802c040459114904258240c0e00918500c83d010751003e10120103c1c500006800000011401000c8241100c44840011270b802160700303603a04102d0307040584050511070414841c0b000c11120300302202c0103914285ea1150b601410160030014050701140c21420107000640300310641c00c0c1c0840265186150103030140d206175200b0741c86401205244c06190180d55180302000d00000e210366600d81e10f1356602c00003500200300503a041396050b2004283c41d8a940300c0c2d070f00e8072030030780d5080340c20026020b2540b8540000284440c3c007402003050b00b00880d903000301c0c2240c2070781d0385400d0064071040d106d6010038803108603 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 953467266 1250 953466016 953466043
    0x60b0307020319030c020c04052e0611012711030609150c210703110412120e0a061103070f0f031701180b01030b0306040305180a0503060a0e 62
    0x4103121090390008020a0450864440114544a41141502140c07202c00f105000f40e044508500c1142c0f0300390f40016485062000c521044905801240c0441c1003050303000381c1e00007802d9405005160b00907694124520000c1c009100d940d050208140d0303100a4904118980320100540f074040102c4100f213201c1d14070000c0c00700c68161502c00b0030241e4400176200498001e1110f40d0121f012804440110707050314000c848000503c0e40640c441404200d0000c10300710805544000350003141000400400080c4240745502d014041203060044080505c5205081484090000b88006840382d1140b8811a889414852500880025503508500c92458000d0810400134103030020032104840c00301419000b6960400b02c0e038948002a4000c100c20300036414400ca801c0300303000c1070100940001c682840d062502080010050313010a140c00e9003620106c001c40c02c082010300d0700c1061800c0540f6400000c940f0040580c0c0f6041c0841c1e16036601400455031603840d1003003414034803030400030480030062 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 953468516 1250 953467266 953467289
    0xc011202090d21030902031b030f060a021306020a0f1104060b040305011407140909130203010903030c030e0a08190c020a080307021e090601080424060915030b04060f06 74
    0x20702d40118030301d1100d58110850303041c2181ca99030f143e100e48960000f55074050018040d9202000d02d40141400449245a062042c4070a06151240c240071880c0034080082015849009040c00c00b41d0a48254200b1011503102004040c00b007406401e0740e0418913003002071b1450941101300130034080c0c10350750482c86204600240c000100241584a901200220103000c5455101c60b40d04846da42d001c2240b0504641042c00381d560f007481d01e03290391600400c038051a040398000340e44c042401e49072a5102a00840e5036500c04010b06501402904c10303040c854005030080c41d09507500e900003405200c8072604c020704038032010184940070b802c101c0103140d0000c001c1400700d035a130344a490341d9500c09001280038222400c2d595580031941d0f142210070050040443e2040d58410300119440b006c002d00c1952441908081c40814400c440707911120f0013030001010030420b0904000b082542d1050000d0307030801100140400c0401c0046c0103040d005544400c0114090307020098844c040c210b240c0000b4120380 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 953469766 1250 953468516 953468539
    0xa1404021011031303081b0c0d11040219020c0f030c0d08182d01090b0403080702180a1d0303162111040e090c060f09191e170c01120209 60
    0x686d09002c4c0c40b0342d04503004141084003214003040d8983c40403801468102c4d07041e020070400074941184659541402801c014180900d04410030a400b901c171320103c02580040c903503840c041c100090003050729401500185611800640400d0341400e0910000d007046001140b02d803d113043d5095a00351000303000380101d001c808a0304440d181c5184036044401d08030b145443c2d40590354001e694540c2210b00c00418941098030b03681300c916855001800407a4403107504090b25071121386641c40c8500414170000000340c54080300701c0c62016407880002d900510f910074020028100e4014807040d4408170b5501d00100d402d1011010030301e07061000d158074440d0358201400e8190402480001e8001c445600c0703030755103454641c0350f0711070707140d808032030b40207030021410000340b81e031030724808000c00c1b40100c040c190010b05131091141c1e5802d100c0380c0d04040b00e212000300c0c1d0070b0074040a2500513405024000300101040d600103020b40d0f603400e03808060380c0c18044140c4001200407180d605840481e08041c05c4003440c3d4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 953471016 1250 953469766 953469773
    0x60d0b0d0b220c06110c1809010e0a0c141f080a050a090f020103050615070624060c031407120306090f1103010e04290a1404021011031303 61
    0x246084402400004039885085480402d8101c40b54005070480c0602c0d2400b401e1010480301510380c038032006558496641e00418648038101d4407a11050f1400304003002d0305002c110380382592001182040103510004507207021071641c5603240308440440401e14080401032022465040c40d10502030742c1c02107110040459541c0090320300e8819081000e08100c6591103900d03441c21142d9194015180003e8004100300550181d03020319009036001305082c28220307451003161031b181d0110104503140794450003074202c0019055040090707002d011551444503410104010300f1203911000140400209014800f40d03101ca1b4411600055081116101a00740d14070020f0080d001510030608081c0c60300b078501c2d80205851041e50210541c060351946035929041d1100c00d038580c05030050b5001242d0541603035840b212000d564140035110070036500140f42405101c021180c0c0300d4840603443c0c0c50001003200607034903010800c2600125080803440c01003103520701032840c0501d010b0888001c0000c01e011040c03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 953472266 1250 953471016 953471033
    0x91404062102010f09180b01090f09141008100f0b040203041b060504151d2224180b12160803040f18090606120501050f0402030606060d0b0d 62
    0x4041c000e8131080550b0b02489002c49075000c1510901e080008a0707a04c04004880c40e4000c0c6139080b00500d401829a07490720640c07500b010103548221170140d039402004c4401800300c5801c0e64000c0280c000c08005a00e8152902d4070f80310100410302e0110b940d00258900807903103a00602c81210040c3c4110348030700d01442d0482038907040b0216a1364030380d18000300080c000d201d4002c850030751354240f1152140c2d04203908152000c070500f00750701021110600e41c8100356107940802403261110000c180f00a8030500c2202c01c101c502280513030342d034030410f00c4181b00080040301b61070f0211039100300c00095441900c0c060700c000300110300580e81d020314500b440589000700000e51100c140c441418080c4459550303012180d07a1b1003980b08210120f00084c90400035840f06030050444052801c801140300300c0269038202c121801c03a004003511030004042a014000c0900c200e035880380030400182200d08043d00043d960340001032515208600001d00d040d14585c40d50854241490041c280350030070340b10741c60481e14 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 953473516 1250 953472266 953472329
    0x109050d0305040f14040b03010504202d0a080a031e0e03070b03091510140a0b0d060314010207050a0602090d0f08072604030b1005121608030a09140406 67
    0x210b5802d205040481d032806112b4140a182d102210621800403004c00d0383c1680e840c184160f50103500d80c8811601a9030007070360803e04503102c446801031681c07417000b000003001c41500a00c4540c2c3c0200d2074040026006000c0050b60040c0710103000b035583c00050202c64a24442c01c401d509801000e01c0026500c440340003841c000e014a0040c1c0300e0504005111150700c0703003b260446214051070800b0000540700442c640910070000e405000003544540f81545203600041da1800e6240d0745200030420b001024815600c2d4107000303c025450440d40ea1074165589643c0350000c0d20540d400a4140703e02d940341402154099803201030407510040f282881a6a6000640c059a0302e90b0440d1528100d0418031610410a2044000c158141425900c500c00c94210003000c5160503003884001088994400c0c5c0100e000c21819002098240c41881d4444c0300c464032a880080280d00900c51074441d240c00c0340400b000c2d510180c8002082d040c00f600060003401d00e5600044115540303074812000c84203040c12520 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 953474766 1250 953473516 953473519
    0x10050409140c04020f09090a110403050a030f090303081f0527060303121609120809150c03160501180f060506010f051606090506011205060603010b0109050d0305040f14 74
    0x22070002c203000a0000764814482c5000d0300d810304006070f1900d45006c00165402c08440c201c0007504820100725011158899041503a50340d0090506108041c0e01c405030000104207850040d062a25556010701000d0000e4680308007840300e14080d0750608928219100103000042550000c0f0460708202c42040311145114407442601d0b00006880e030600100315003805003684141e140d55603900c00da5814210351151103100700401841c0028503405031001d550700d5513020320240c40e80c6000c0700f0b00700543d1802c44080c500084009101c6944a8100071041d6940405a104154070444061400ba40101424515040c5008071b0500c0c0700c0521500003503e0144a00c1144100400c1d25088010b607807102d5461420030010320704100032031022070a40b030f0f00100c00b17101c0c210100b09010950340c0d0301c1c1016003d800600405000303950a00078000e0800c11150400b00c1600204072080040c00001e11901050046034011101d2480d80810540300c1e5084800918030b041c0d140014586032018150440a01440c01c0d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 953476016 1250 953474766 953474773
    0x8060d111e0a0515031b0f0f041401080f070f0c08030a020310140a0603020c01090c060e0307140603060118090c050a0e09060d02240309060a0e12121005040914 70
    0x120380c0f8102110036521341d51a070103a01d400e5540340401200c5600030a803500c08941014082080c02c40c1c3e601c03000d000140d000a000c10b882d90304200c0b550300e8445241d0902c034100b1001c0e00500403241941900d00781c0000140c50486441c014550b01074414281d8848000c02c1230314004200454032040707602450040c2c0b444030f03401c12216550703440300c2c446501c445103180d03000c1c0304001c0410105000e5401012582c0c103480000c148880240c03100b002440e00c51340120045003c40135219441d2a051000c24007800c40001c00441049074080810324a000042000d170500040c0300746000284c2c85100762200800c0c5103401030001001c0000e004003103800c10b0410001103072001388843c86624210031241e103e500068071240c8048210340810004a074410034040c420816284072400c20a0182d0040d4803960049005146c2401c3c529403410817616241000d220a0700302a034820441d03c0c84408840c404880902c3c2e80d0081d0b21044131800c401000da13481254000e190001a40420058010300740e104110902034 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 953477266 1250 953476016 953476019
    0x305060117160c0c1707061107060e0a230a0503071202060d061203020330060d020613060c0c0803070803070c170d0c11070b041715180105090a020108060d111e0a 71
    0x280ca0381074080308c0c0800160040c440030310081b407103504841d03600c3d0801410095130503907903141200d030320f10030b40c08149032910000030400c102d041100d0351000070301c0b017a001400b18501c1c00b10260a17140d4061002445400001f0b01d03203507207410300d80125000c2c1040461030500507407546400ba40d00d52007604400045802410440444400940004208606c1701d140b41103503540c04003046501492130300d04a034000c174144402c54080038410400005847c0036101c14a03880c200381400401141c3c43ea0008105500c200008400a45258143c13500010142406400752101d03180481c0301251019030044d0690011682d003100721440c0d00b00412510194131014484170007a025180c0b030328001d010340003401c5002c0008020300c1d01c0f440c0007072000a000b00c058403082005049251a400e20a0310742d44440841003504d0840048288181904840c00d60001d125040f22640043c0413141c009002d2231184204400032000d000c2016823240940034014200c00f0380c4030920070001884446005058040c1101850 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 953478516 1250 953477266 953477279
    0x5100b0c1e0106051021060b0a030b0a08031e04051f030f0509060117010f0f020a021006050d0b04051014090d0903020303120603030f0c0d0305060117160c0c1707 71
    0x100419288085e00800c9803100c000410303201c10f0340c5400050b41d400c81313920704103400c0c1c01c0910425024141c100655070750b4a24200c0021f00391a907901e8000d10410b15084100711000c1d0002c00c40e00000034507413410080108441d240d25542c0915400280c1011050040d04907500c0b0352015160700450a4808001c401c5d81060407008a420454a2030555844240144021402060081ca11200c1400045480300e091a10f000c29603460600700803103160040740400d0602d40602080c0c50108032004208440d40c6884d0000e4804250008043c000004d030802003010710009000300d45e00402414814001003000100d4429804000c40e260403090054501d204c908a21900e003440403250001d000b181450003145164140180180c040d542c184010400030130001e0340035025040360f600c910058800c1d2203001d0350190030340b800106440c0c1040040e1102c42c200a80d00e04280380c0186812203081052070701d10710706075003024001e80301a000c0388202d040080c0c0030440320241044060301e00290754140ea554036 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 953479766 1250 953478516 953478521
    0xc0d0e03070b130317060307180914060609090d0206041b0806070e102c010c1a0109050f04050a06091707050f070909230c1203030f070e06090405100b0c1e01 69
    0x205c07600e52503004101c1c10402da004849c003036802148900000101c030072451351523011400c0d169400d103505030042810032400d8648007920703d502005601c0608102664888002d4440c0e100034402482ea030320814031100e00d070110342d4101c1301031b00710340c01150658204400c01a01e1488202015407158103d03804114542d4443d8400740d800048035803206070712080c272610104a000c06c0c41c802038100003920101c03001083c4d4441c10092500d070000125071b240e506083c2d80c5001d980c4000c0c100708170701440f8401c0c000081c000103441015140c1144000130840d0b9280740c1442c400b0148000c0c018900b60200d03690b030502c000400c008490004c801d08031360030540d40700450f00c25100c3c00340b40a0324035280b22031303905a038015907480300c0080c28946050354159900800010b035900781c182d170f10083d02c0e48080304000185090410081d0810841c3c01e05000c2000700c034001448600c82da40d120b5004d1074458001c124000c600ca1a4003010b4440350b0340c82130f180d10030030a44070394507801240d1890403860001081c00500383c040c03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 953481016 1250 953479766 953479771
    0x60504020901050715020c0a03080709080d080a050703151512050402010c170405061314241c0903020604020a0e010f0605220305061504050c0d0e03070b130317 70
    0x10384a15042ca102c0c2e491794000d40701e1042441c2c01140c0c007000411000f040034482c01124520075219a00d981c00c102c1c034024009603135500a0316195110180616070a50020407056200d5560600810550740c0d15004402601013500d400e60362002950001c6081301a4101c0000e2136007165403103121080305030b49500c051b1070b020b8070068003048010350740303c0c0828100340c41c0c040300c2c211170303c08070380b411340d5881c04100b190303001e400082040d100c1c404003031011040c004041208070000301c2da152501e1080300170750899480740b41496102c6d080c000071244584540ca10001403510006042040b800105080c003035281c4100b250200d206a0b070741500491191303c5403800b40e05854030b0004035440c0c9c86c1440415602d9500860058801e00502032400c214030031160075510103144104090300440c01c1c090302220078400031f65901c51140e800d05081103006008001590490301d100407010030588140d048090861099207000f4285901a5041051181c0c00d00c400b264054400d0792207560380c0502c0803440c0000d0070207 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 953482266 1250 953481016 953481019
    0x60b0c24010506091504030807060e032b06051908070b0403050a03051312050c01030b01030c050315010504031b1401030b010c0b0a0b060a03060e1e01170703060509010b040605040209 80
    0x304010b02107810b11002512500002800030544006804d04006041c1c00c10f40c41100e184200090082c100007840c0074825002c0304075001182060802e44403051456010300f4050005503042c441c0b409078400c0398100d58010080070700ad0307039903d0300c08126031914407502c1c3c0a28034842c4184440001c81d00321340001c58045a41040c01b4146040c486ea40c00c48480d44503404d000d10384402c0301e602044e00c50360326203006840c902c43c800418200300c640001500780d0b000214400e040c14074140305040801c0d01304045035842600d10f4440c2042454000042e030755030040350005001c80352110100e294911540000c08103441c03039a490b61170720011190045040d01c060358415400035031460a000005500c4000300b0390009120900400c0b400c00c2400445c3d5180c009070110b00001c0e0300c6010402062240d40301c2140c204010810280c0c4040f100c401c1028400c0041c031809407400e00310009d0313502e8030105000f118050350b44104144524186207503124003811035182501d2065180500000700341c50305100315a81d0400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 953483516 1250 953482266 953482333
    0x80a0b010602150403141c0e010506010302041805090a12090807141008090a06020d1a0406030803010308031b040609030b06121f0f020433080609090f01060b0c 70
    0x441740c2e42241c0307240048105d808010424412150140c452000401e00007548180010380c09103c400f8040c01c0d50409031801c0e052510420007404096084650b00d0301003841c40340c0204031a10342c210301900d801101c4901500d01c400c400f40111180b60b000080c4412208054110798030181c40b0091809104c8208020907403020241407441036081c059100141e000c01c6510076982108429100e00c41a68019019040303003568a030000b00c1d40c2d00300c0720414210703c1c4003560b04220050840d1754000142c0300c1804050848403010000510340c400a02d102c440c0d0155141c4c0003525032b0364070341000e441e03001ca0340421904d0a0000000a6103420003018060320107403980010240d40030145100071082d200301e0003192020b52500c0c0c07410506412030004100400e40d0a511641c85c82d208c2c1d40d08000000f1010700741402e10340c1941c6080400394491409038219004503100c40c01707510f4040f809450288a80316420655080881c005034050580000d400c1d100d400805030b41840041355481d0304000b0000daa0b41c10000c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 953484766 1250 953483516 953483521
    0x30b1503100507031506050406110105010f03060b0a180b0a090b0f0f06040305061806010501050f0909220606060206060f150915130302031b06070b041b080a0b01060215 74
    0x4200e6040b69800c02c4072802d00044140c428450200c20550319004407010840c0001e04001666005414100e80f00b04034008202d50750411740142405441e07440007400842d2181144c0200d0760b10703501076000508614201039080c06003214800081e007040400c4501c900c2038020005035050007030142512018004009004400841e000c009403502e0700d0076040d401110a210100c00204100010303800740e0002e18010401c071112094051600301c05810050401c001840384494081c030502c1a40c280c0d941c1151951241e64640c000200d43e11484604403030800c40d40e0380d4803414403040c2d034800e50a07201d4a50a03504c0540c1daa00501070b8105044041c56000b1004181c0e0f1004500048090120504001c10544114000b10035140040e04626a094a0b40040c00e00030407c42c07900700090f0307450b00903101399500348502d01c03030009040f070003600e8000c0d000c0949500021f0802c516010546207501c04048640d02040d00c1d104403a035250b0807100c00719140da4911001150840c000241026020a00001403910380d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 953486016 1250 953484766 953484793
    0x906060a1d1f17120f09120705060c03030906070e060f0a0c0c0e040c05040e1009050a12080106093303091e03080906040210052206050d0f0b010801050d080919030b1503 74
    0x24554a41f440442d025500c0d01040c103640314002456089150b900843d22410060021801d081000d002d680a02c0003141203d80c1316200e52042e80d2103100a04180340c2c07101c401030005d17224400424030080c0b054110b4040880c0114006540c607010754056000f0b9107038a81c4820502017240d0100300e10ba01e155008000d646002c2c00c00d604041c41081c440d43c1524590b02e1903a07240e100c1c2401d032070300d1080480c654900501410303510005002c02480d40e90425001c11800300d4516403070305008000c2003d011241c0304a00800c501a812040e8020342c800080320024004850062280340781d0001100042d82580106140500004819000b6a0010845031b18002c44940c151456808441c4405003005100764003a400030040c0041e030002d0010ba161699281054001c090448900d0102d005100d8500b80340b00b00d0340d0741c0c400c14840c1505e00a0381d170f515500015092124450094811407940494050791044400858617900401c0700e00c00c0c464000c0c80c2d100d50824102d154080011a509544a500102c20a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 953487266 1250 953486016 953486029
    0xf0d0e0a150222090e0d030908090906031606030c200304050904020d08070303020d0c030e0c01050a052817090a0b0606040306090b0906060a1d1f17120f09 68
    0x40d407004100e07805803e0f101c14000880030040394008504640c2d940c4c41c0d5200814280300349451101180303030411030100755a1310030700503014416000380070340821800a1440c3e181006494020850007411182c020394500c0010f0140038a0388400000903101c3c826820034004008500c1120b80c0d0110165003018100414403406100041003a40e00c1b0300000c2c0c020000c155800c000f800c9480c0030350f0300565035407503008095050725070a00c4490101440d080c0043d465620101c0c0f03014200b0700918059648007600c00044646000b02d00f80b0460422080315945080810455001d52007556900e515004042c80112140421b4080390a90100d40000350501c002a50001c041503200d00c0c000c2c002801c2c02d4403602ca00048440703082040f44d580000d001884010402008031a5000408940d03001400741400300350710100544062040701c00b807801d808941e4080415107842c07800c81c0149803c200c041d541c0d81d40010071401c0010340514a0050711850000c00d6030cc002110003c0b40703801070b05440d00130800d060151 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 953488516 1250 953487266 953487277
    0x14120f070203091201020703020d17160e12010b1f0f0c061b030b31020d0b1f030f1a0111010e060106030609060e160809120f0d0e0a1502 60
    0x31070008000d0305103d0b668081c07400b149000c0b4100010b0311030304c491402034640308441d0120824020a03014003000c1c0c102d4071084940c00842e401541c4c8450012080542e4065008070840d81e0242c203803e50004801c0c01588246400c2104464454500100680c010184c280030f12010700003403603503100310041a00a0b42c07004070342031144500207612204d0078070418424041d00d0804000a0302c0746c484100600d040040e005100b1070025280b1000b07202550b0b106441000c1849880643c1e802162010101c1140d912920f104113020301303224070710007071a034400450b1b8241c0d44154002c0b92801202445140705031044040c1546040030044100001e6001501c141804c009480d20070b64075081c000c3c59170a0140002402008252000301d580c6052081e601309560041c0c0240341750b8042c05007000300c20b8880070700780100e40c00c440c05c0004042c1c0314840d60b00d0030003420041c842600040050391b110384602940007001c101c120b0250400405a41d418210346451a540018041c3d11018200c600540703000e900405 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 953489766 1250 953488516 953488531
    0x90c0703201c0807031a0a140f04110a110106050d1e05100e070e0412031e0c0e120d0c030f0329010908030f07080702040902060310030314120f 63
    0x50b10210304041c0001074200078102c11000811001c24804859007501071a55882d07034052208249892003004600103013168801c44481c0c6030684034074001c5844039043c048400b00e018005210310100c1c05134809142e0b1119104c0d40000d00543c0c45481c0320b071018030501e0305503040141078118040507038682140700b1003030070030300c51030315900c0c0c12a08000307002080510807000d0408400710b41c080c0210b500c141046503a82c001c1041e25908010000011060260310340510443d00340010100c606c16040a0030b00030f03891a6550752440c203007440014070303004401141801c4d404c03100d4070400025901034540702e450510381d16000c03500d00170600340002c0c0030b0800c0050000051030000b81c014040f441e001c0c9134040a01007800b600f50195a0301c4013950b40a00030340e015088480046242c44140c02c0d042401c0c0c8200c80b03018102c10300200e204000c641d03584d0010303505103070001d003000e89904002d04404a104200d1008a01064118070641a0440d5200030303a02800ba20343c0b0742811030344d521a20801d04140090950 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 953491016 1250 953489766 953489773
    0x50f0709031a1b03070f0801050d08030f0a060b0a030204031509030e0f131404050f071802070804050402030c0316020d0e0913050601080a120201051303261302090c070320 75
    0x6610742000c3c00e01840c407400341a03449000c0e9100150001d040c904060f04024000d950b03191031540400c84040440380c0003800159040d03426520411070b10002c1000d5000400c84450010740003803825419000b030420360f07015140c001c01c1c03011034551610484030031000c000c01040519103912028501a01c10420b40c00010304000e08111802940c0701c102c810711640042c201241038248400c6c0103042180002803001c22004102083c2808000641da034900000c10800640015910702044040c900f59802004043e0055499050020034940e0a4108a0b8000b18200000704080511840010803078801a0b81703032204c14448118905005d02e00c4401130401181c980088852000144100401402402c1c9400500305412182c50599101c01030b0600c00d0045a04100038070014001100005000340ea050810824028800d1031101444001900c00769025010004000e282c0c1500301030010854400c0758400300340d0391200040c2c2070328089c2800107030000314003140d02440503d00b0600100341491007400c9 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 953492266 1250 953491016 953491051
    0x20d1b14010c02010218090709050d0510020d091a0105060307051e04060f080f070206010e0a0b0a06030b13090b16170a0f391809050f0709031a 63
    0x6682510b214104180050b0760020b425060a03c1c07144103c0d600f00400ca0b000b5a8030706100c100140107c042e4003e1038841c0f0301100c20318080100c01c0080c40c1c100348074007400307649403080348030b0000080076203013001c0e01da100580b8030b5a120a0303011001e20303058920080000b411a2078a4608442a80285001c1013000301843c603000c0000803442c0140c8024605076640700d11001c2c541600070722041c0041c1c40b100c802440d00040c0300030182c020078105e054410060f0281c4590392140d00440140c510342001c160410000e01000c01d0441d4160001010001e00751940000c1d1121540c4482c1124429000a05036070b000502050782d00e81040d00031444007515241145110b1001008103140810035070707203010b0b115502c4d0a004c805c51254013070807003208c003c07035044014903400703080c000201d00815205100648040804610481c050241103070314a8201c8600382199864650b00d500a00040d6502d00b800700740500010317a030705c3c0300e07250070000c0c0c07540080340400e5400441d140b0880200b02070302c3d0310b025000c4d1810 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 953493516 1250 953492266 953492303
    0x903040f03050102130b03011514070b071206300c08060c090307050a03020108060d26031b0a050a080712091b0806090a170d06030c15020d1b 62
    0x40c0c00003840c0035000042e503e01500c008070914440540c031020310b455060004100d1400648200c0711000c59904080c841c4c0c142c07a846a44407840b81d000000c00780141c00f810b00206562191112002a40841c403c0001da07490700d1002c9074490030010b4820541004160001404824092420300da40c85601403d81c055158180d01e42840c00407140e14240e0100420b0604c118075081101100a010540c0e081d8a15821a00005d040c140300820884c040d10002045034100b140c4446040c1c601240281148003104400769280c600d035000345c5595451240e03840c00c1141541d008421121914420b484541c5048006102a030308407038014408030501400321900041e00b401c1c1c1c01040b400d1840b03504402c8802000c80f405144014240c0c01040c41ca5000100f0070020000c00036041e800b03660440081184106207440c1d0002a2145445903600e003424044000200f1030358110700820f480c50411031942050f40000c080343d481003103000143c001900303542c6103590320321031400541484d8000d20304152038040c18407 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 953494766 1250 953493516 953493539
    0x510030f050f0d020a0516030309090b0d05060a0b04050a050606120c04080a06231009020c0a02030a06020a020d0806060a0e041803020c030c191512051005120d08010e090304 76
    0x2a08000985c010007180d9042280a00c0000d01e80f2049a2290369041d096880080c07030300e20f20340540000c0540c0e601c1030520039542d6120300858650b02c60216912460318051910142c0314048019009a0038840031404642040c066180b2035a0040c0045080c05401e41199190b1030300a4041d4076620070802011411141c00e11400070740e107009102c003007150510301e03c4a662503003002103100d50700d003404424402c20312000319442046a16a040c0541c44009480c0c2041c00d020355160000c5d45072184007019410001107401520b0910b4050302039440c1ba0102d41015941650120348407907009408004a001d12401038040c0009980c000d8000181401e049103440c4041e00d25036403d80141e4030a00141310f80740b808002414000c4425200c0d441072104d82d250802c1e204415001c0c074032a8100c04101d002c4854421035040041e511a00c900b4412811301140c0b108040c445402840c2c0241600e181c1203090030303000107081c0356011441e9079201061f0728140603410a09800740c48409240010400002c0c01290034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 953496016 1250 953494766 953494783
    0x30e0105041a030105091e040204020c030d150e06090f0f130f0507291903150b04030b0105010516060b010203040b04060315120b13150203070f020c01030510030f050f 73
    0x14901643ca504040810a00c0880100302641c41c154035090101c0d16140207039056003007035042d100540c0710503181c110740d410b502038003406d0300c031303c038074000c0002402c0c000c00c5990421201400c841c2822034940c001407042c4030004513800d90799a01d40c00007082115500380c080c15440030360080c107000c50b0380890f550f0a441781a46041680c09900040c0240480703507224030304891400c0951400b03500490213083d6031105005005500d015518420a000403640c002c0e0450354031181c02d91440f00382603845041d491401d8100740000d4490884e80c60001c580c0c1c2d402003045480c0088002f07000b1000c00380580c1c641014040c0e810074981140010700c00081c5020b5084003074405030140342c40114a1242c41c03280c092101600360302000c2050070754804100411840c8440c0390300215000c0c4d6008201076035082841c15000344e02101e00110f8400000c104070350b9401090b0010b04c8070207500303031054511002e0044040d540243d03414460042c48a100304000341c0000300034a4058072550503a203240c201040031a0800203034 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 953497266 1250 953496016 953496059
    0x102030a0818240601080702070807120c09021c11071104020705010b040c030621030f08280c080f0c3406050619080303010608040503070b01080309010e0303040b07030e010504 77
    0x110000d03c1007960700881d019034441f46500c020b000043c03420200582e0782946104401c200101c1d48040030070722070b8080203030b00501034960007555600b2b002e2840d040940c1c401083c1094045c078040a400d0f00050440031118500d81200720743c5090307225074013000700030340c0009400c44145d969600c044d0b605407518080c00c010091341d030b20009546454271404020300844058040b10b1446004083c100082e00002c0b070041c24029498902c1c219625405ca000400384400304c0c0d121803130a0300507944500050790304900f51214896070780c0d1540f911000c172600000c40094964004020303060011555407402245008030000100345807000740c010511182c01d40e0b10000c50261503107501c07041048642e0500fa07121031780714000002c8141c0c1c07061410402a8503030106006030820803149201180c240a001c10942e0030300c540080c0c14281c6540d5544405669a10448030710740031410102040394280380100c2030b00d0031200d081a16501d8106299001c0343c690900d410316605100040c000881c000078401c0501020504 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 953498516 1250 953497266 953497333
    0x100206090304271a1003020408030a082a0315010527040b130c03200306091005180f01050a030c260d05180a060e0f041e02090406050102030a0818 64
    0x40c1a07050182c540f5407103240b80f05041c0100801c00c1000000000c48850711403a11301881152240d940304001c0b07556034dc622040803c2c00ba002c108144418a00450054070210740c540c81c1c150300f140c0195240d00900071100c2c01544660f0100901c594013031011002090000c00c0060000d55040000e001d1698412230b000ca01c540d50352607443c2c01c940500c00d6400081d120703030306131150101d521130704207071440003c1ca0300e8003403100d80d03000c1400a520304266001034440200074440c091100c44168000c00c03021540d0a4080840b10b000040310300300044d2480980e900100404292401c14001c110280c0d0740319a500c10084401007440c46c0c645082c85010180940c1d80d90303103175980c0490b40c8280c1c84c01042c0b105151044503441d44c1009801e801002c00c42ea2400165100801c207104000081e005010104440320428019100360614420641c014013001400700c4003006001d48030001203949004011080d00401c0c492000700300e043c03c0c40140d954465a110045a59178443c088441c0d0b2804410400b0084103032 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 953499766 1250 953498516 953498561
    0x512070f0209010b04320409110a050913062a0203070b060f0d020f0111060a1e110901050f040b040f030201030e15011401020a0f0b040210020609030427 67
    0x504122514010304d0f110303080c142041e0070030000258020041c456180b004030640320300c030403030484ca0102c848001c00062003000740314040d00b803040324081d081401303034030810840c2004295440d001b90441e019514000a10350202c0d0682e0301e0000821035810b548034032507604494540c903040f555100c9041c120056001e541c40303084034600541281e00140c452489540484030340321194640011120a46404030399121b403034440800143e032a04a00100e210b501c4c050f410070000b61840f25040310701803071031031080102c403030700551600022105440d2407240038120400c100b1003079602c00d0002d0075110400b4030540740f80581c0c899100041da4042da0040d0740690002e0307010402d540e0036100e02800c0f4400c51001c0d00540410036040c4841c400b05004038290746e0401c1284c1c1943c0d034800c100c05c0000640c005c201044460084c1014000b419080707a0481c4202c0306140000d50441c8045a8240260780300710043d401d00c1d0401055070455018100c68107010400100381c84030742d060a0080c011102c24651400d92504c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 953501016 1250 953499766 953499769
    0x60f110c060a0906021b0f04020a12060308130504110703180f030308100902090102071a07050f0303181c0e131e06080102090105030c0d0b0d0809030d110d0c0512070f02 74
    0x5030b03c0e02074850201381a003d50b0005032195040000707c2d01c411134006030b41c0e41a0502c1614450401e5642541c0e02d441d000e408020022601e00070300a81503014410140c6550b175030104400d449000640f4001201c0500100000034060000d461201c00d2a0750460485510303521840c40240084c0d00a4000860a1003840002100031039a80050301c0c2d4410190300c1d028035900080c0d40c890040c8074000c1001000320300c15042c01c81d44010f0f10300055000c02039035010801041c1c081da4940040d80c4140801c01740c034a40444c0c10500080c100c10060300522060a0740007039034000e8a01141e1094002d4008001c4034901246410b1449010424012414600b00d500e100031844811602e140d00607411582c0304114401284e0703088400e50303500121009140303540300e074140a0b12001d00b200254040d04041caa82c050f5080041e170a0250800d10019030407183c242c0f5045808407045ca6041d00100041c5d08404100d01c1d4082c411b20448648a000b442201e4440100c404416810740c05100c050300e12885115030f035000c5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 953502266 1250 953501016 953501023
    0xb0f030a05012a050711040b0406120c171009050c0405130b010b040f090b0301180320160b2206110f03190f0e0901030c0311030106060f110c060a090602 67
    0x1070240c0d00e0f4070080300c07948040c000d401032096120140402c5030f45200c49540b5600c5d904840c022520203001400810b5554400d1605900030101c00c4810030101034010508000b00300307900d4860006040100085000390042000400075103005550724000c1c280111820b071160f0042900810925898018802d000d003440c1d8010390060b0080d0340390000800c01085070011103d0000251074140000007102500ca01c000f034014200f030b4181c50309101415108009041c1c004409012400d120003042c02c811541241b041d0b100d601c54138200e4042240c0c1e45007404841404000741c40c2e40701000300c903080820340300d040000510450750300403400602c050710080d40641c0f09128444484040707800550405804221400006160038941010040d101c5820b1840500c40d0b0034030340045101808480307540d6100e0a043d100ea07002404140e60344010b942003842c06050500c500c0b011941e6540c2e540c01c003240740c5a8202d078107889407103045180388603000c407601107a51410014250a201500d071482d05a00d020700103400c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 953503516 1250 953502266 953502311
    0x4090f110d0503090415120b1f080d050d23060f01090e061002030417030a0306080307050c0f040f0e251a0d020c06041103010e07050607060b0f030a0501 67
    0x681c1000d002000090000802e4540c3c3c042c01325004104c03c0602c0f0304898202034103a03c1851460054030381c12083c03001c400755082c022844090000002c003040c02e440d03511140244545101ea6100d481161000f602c9480900307421400e1500c01308281c07c0700300054860005015402c10117040d002d0500820303150040c0c40d001503200a080c00f55500389452034004400e140108294043c040d4041c1e071f04010341c8284101c4000c0c0c0000c0f13905201005148050640c0c0e50400c407a44400b003494002c0124100100006642c84079600c04000c0c00e14411000901c225402d141c8a081e41241d111144491149007034041d01c142200c245006000203141d40b1204001c13500c55282c00240704403260000d0120300789003183d42c000e101c0c02041701a40c680805410300028400e20448007950701810050104110842140010303044040380244145031441d002d0503164015031003201d5200e401040908000780480d001070707101c4034004001c03800900700100803038100070b4201e008940c04c0c0d6496081c11440240d000f580030303 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 953504766 1250 953503516 953503519
    0x2090f041a04050711030d0504081306030c0207170607030c090f0b030f1006090e090312040f1a070e12010209190e0c09100c02030c0307150813020f1e04090f11 70
    0x940c0d2200d03030891b40c4911031841c0b00d03048692680b00003021300025601f141c4110780c1c2011444803407a0b66040050040040d4000e41c00140181100041c240f201c040240008020580c080c20607034580d191f00703a000b048200141003e108401c040000c040300150000380080c1180482c1c02e0740c3e450007103400c20b17000c4401041e1600c441c0448030240882175200c05104c06950020a20400989500f0f90301071640c010b2000010100c001c1a0801c003c0000440031b640c5064424840c00800510030b0224101d00d6004481c032100145032400380107454074003107030b0100700d29128400042c036115802010901e0400540110160801005420401c81c2d842901c440e034818910801e5a0800c044240010601c928001070034041240400c202000d55900313214000078868010100c03004203660740248401040302190b40400318000c0000a0729605d034540d02200c142c2d41c001c010b070b40d240342d400c030400440d4628032010110088007a04a080191600c0c0308107030026019404902c00b1341207a16245050704000242c0c079 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 953506016 1250 953504766 953504777
    0x5070e0a080102040e040312060302060a0905041d0c01230406180e010810111611011b020d0b041406070c020906042906071b0608011703030a02090f041a040507 70
    0xc03c0170f0300c9205102c80d000b81d0f05151031400000d00303a10307140160620342c102035032041000503490386154000c1403140807108140d03002d01440311030300700001000446032a115445e80140000c0000366206154546107240710300c8202e04959903603800410070360003941250010800300d03410901c0742982c00050a000700a0744500d450741d5030500c00e00c551200d1445026100440d2586d07a40b0590880b00802c1d10078191090b04940f5106926003041400da80c2441172a60200c0e0004110300c00b402d00c90b081d86803e180d009024504003500e150348110b0034800041040e2641d1222071030f1020440814000c3c3c5001d400c1c40e40e10394040200034010051402405403103148103c2c600b0740d007240c0071985d12020105008c0380e0140460701c20390550100307440c0d11480500070100400344c200c9c0c03600d0f4044a4562800d44a00340c0d5001026030302c8502141c02c01204c11140b00c005d5005000041c11f185081d001050a5100503203007100200e8810041029030380701a1174440044418426050f107030034248901c5034010644d2514 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 953507266 1250 953506016 953506019
    0x40b060d0c0b0708070209090a020109121e031b05070e07050301140d08090312071109041709220e0609010605010903110424080724030506010e0405070e0a08010204 72
    0x85104402140c07140500c2d50300082061020311601d8010381c1c00c81078014141300ca05180902c0c505440d00b5071848200c0c0400c00b00c43e0041032491001c400c1c210600da12400b210071107010504105c4200c44048070840c10841005e9a1450f81006824081c039454880d800401100e41040c19003400e0030070040003038041101c1400100300040003041c9502070b992040e900c10b84200c485052443c0303940300308000c83c2e4142c49030b8000003000c020040000e008540c026503010310810481c4007004044401940c000d000010b180c40da00c5856400c0c040200240d00700200b420705030210f2180000c851600c032030600d40074260341d45400d040440082c0000381d48083c00340020801e81d424540040d0481d0303014040034240d601c131103a00400ca074403103034003004408464890740b50040314080d0703030012040da4601440e00c0ca03020307000d80080c803c440d24041f0706401a01141c1044501d280d0725044004182c002c102c0c40c104020307000413140e5178849115590080c0701c1603803440301500725a001d101e038264841d0320407103440c0e104000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 953508516 1250 953507266 953507273
    0x5010f09030f0f092303160f0b0d021c0e01050901110a0f09120501151e030618200307050604050a170f010c020304210b0f0718030b040b060d 62
    0x240d40d80e850900d414070240109860800302c0304040319420940c4500171000c070a4403840d8100c5600302c0d051804800321194174180d0301e8040945681ca11811441c1d4900c2c4106000c0480c100d0007401400f0f446402c010f0420301000f62682803514035400c21158242d0341d00c0f0b07401c0c424100703004441d03000304002c009004850000b800d82d0480e11030707031481c201080780510503514114410251200141101c41d50543c2e1a81c680c1000d40c0245410689000c01c013480c0d0100207a03119080c0025107264000c3c1c1c0404000c98030f1502c2c1c0030043e01c00748480c4c0c1300ca804595001400102c2c0341415002d03071000d40015072904410301041c94038101e031035000984121400d05c0108030302c1d80c0d030b00d41041c1600c0141c04002007006041c01942d00d802050700c0350403015420a007107410415030000140c4203d44e020005030b0300c0ba0038140e92540742c08111030009415111200005082224140c2450f500240c07036160400c4401e86200b038401a040c6a0b4204944a07800b181c24001404602c0d403c4623008401111410480400390384c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 953509766 1250 953508516 953508527
    0x30f0e09040213110c060c0901110d0c060b06070f1a06011b06020903010b0933011b2402280804060e030f030108010b12120a05090a080f060405010f0903 67
    0x22406a00c8a8a03080140030b0000c0341310903904615024000c4402c030381000303084880c10b0307000000d14500140b08603000780c0e08181c0004a5640340007480d00d40185243c0c290b00c2d02005800210401e80e00b188080040c1000100214010101d42d80101c07a00d048084101d2241030b072000000c1c0c072841c104104070041a410031580e040090f4840d900500c010b0340c910648000c280903104e048041503201c0c211038200070640241da10403d0450806e102a15190105000329400e4149410034583c001146c94951850003c401d00d01d1020880c0600060805c0c590764030800440001c81284014150750042800d400c40d1051548074000000f0120500c400b29a4044000b014481300800181100d6100c0d20201803445051045440300d10f04201c42075035960f101c0001d10301900c0d0804510f07002c2d01e200c0d000318034404404141004601c115403121340c54620507039012105604210030780341d84106402c0000403249420001e41007030704542d034050b203143e10b4581402405c40d407000c0b05130364119081c03492500c000b07a840b4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 953511016 1250 953509766 953509789
    0x1c14040f020a030c1404151a03150405040b09060708040f020607032001090c050901053105042f010212091c051c09080705010f02030903060901150501031a040513060504030f0e090402 80
    0x2340041502e80c0d4411009582aa02c1c01d03002c150040d1800d01800140141c1f41c00300d1703204154040c21220700c0c0e240c40b1403c80c1c4000e0200c501804428080380c4410062130b140d070091042030302034507044c4000d0296500d07115040903101141d1081e82e642c0d41900c030402c84135188103401420b088074008a203600d814046000c5a04800d0228099100c0020265846130280064640d40200c14820072061805180446001001450307078803100c0c4100c5403102d130001c20f0100c4480a1101a13000e40810ba00302042485650000981340b917012201c040030b100340714201d88100c0520f074008c9000307050000800c0380b1000a4401c81c8004810400c884400303201070003001034000704844003860001486919806d00b2400d5000b0b5551165050042200b03001e0304400540040380c0b010110b40301c0b18295607072040190111002402c901a5001030b4012050091505a0100d40c3c05240103a00011034401d6944d010121041240d0450100b1828040405900c5d0b00050b0110880c40a403060302e25814281c0001e0440000e9 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 953512266 1250 953511016 953511059
    0x12070b0f07050a05010c0509040b031b1207170d1e0e090613051005040b011704060e16031a01090c0c06150b0408031c14040f020a030c140415 62
    0x740d0101044810000008103c0c1c0201c001c002d2440a81c000408a81c0980c48252040d030074840420f03101e1801040d486090030403c81120404400001400480b01145503840c0076802a8040010100e0400303400b10400d0002c000641201d561707444029101e07a00007500c900b40025055007410000b60052000810f00a040314034494503074408000036140e5840c40074440c841802e02c01401910f494640320300c000c0c0c54003260b040c417840341c0c044011101789081d07a0340000501a0300c400302e404a80c480e40b02c101210100002c0c0c841c0092024540c00c420003142d441241c0f1100c0008102c03205062813481c2a003d81203a402c24040f074005510300501c5119a0701d40900050780e11218005940305402c0c0c410014143c5104050302c560791040002e0301c82d004401c2883c60a82801ca010710360072068854200b42400e0b14000b0000342c0c8840c1c8444001803000c01040382c011a492a022011880d803545050007000000d030000700f50346042c5e043c40180c4103040c201001c40c0c0c9007104140048000c00c42d00c40c150760003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 953513516 1250 953512266 953512297
    0xf032803120608190512040608161407141f0209040605031b040203042612010b0306010f0f020a0c06110c060304020607030c05030c01090b040212060c0a030b011b08030103290a1a030114010512070b 86
    0x30300a0001b07051a8402a030b0000c419413b41140307040020640142a071f01e802114104013081d62001450b03156030800d5150712424510388001c041c980f4180c0c2c059a00a1301410b9880940740c4000b6000c240c2c912490030021006030086180c0003040c400c940e00d1030242c2640030b24039013181808000a4451441e0304440c106000d4106403600060380300b04a803000e5a0f81005402400c2941d5000240ca201190b030b12002081c00b900450906c11b040c85422030b40582c0c2d015040602d011810349040700d60001c507440460b145d0108205a1500807002d0146404c00390007101226035509080c0704008418003251002002d0350002e00400120705803600503920700c0030040c10007090b06c68044004070360303088001441c81080b0074980c0454040c050220702850580c1e00c01d201800074110300e030709060540c5880c40c1e000c000e1028140c001801d0b91b4141c0e0402180e16a0441841104400210000382924012400000c60034503c800410103894441c02000021031214041c0c04001e0420107260389a11510304e24800303165 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 953514766 1250 953513516 953513543
    0x40c0c170c0d051b07031b08010527190b1503010c080a150308030c040603110f04050d0303180b07030b040e0c0f032803120608190512040608161407 65
    0x7031504e00038560005500c400c1c1c0e0411a228a040101060360182860800d0740e420303004212402c0510a050041c050490881c034503c2030000446100307414004418103c0c011021028400781410143c00e03922403003100d2280e00ca02d000741040d00c1207018220183c2c800c2e8142403c40c11001d412208064100c51394a0000c04c810040100101d0981101e91005002c04400400c00900070005400780c01a034026941c14800200e040f90414101c4c02108000260140100820842c42c80c4c0380c4034a034070700e40c803908010584070651100c590108100c03142c20340e04c050b40034080102496062040c45030180045070200300441d1030483c0940d031414540760b1980140c401000b9803d141d03808004c1852209040d10ba00c4600c1d41d4460700c1c01081074001c0208501141c4005610811070585010703007001c1c6d50801005016a55802490780c1c4206417150040d151400b48101c0d070740f51075115400070800740c05552070300c880e242001003581451503285904141006201140e806117100503170200c6542e40e0b0490700089001c0d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 953516016 1250 953514766 953514787
    0xd03020a021f20010e120714030406080f06040f0606030207030e0603130f15060623040608061c020a060f0912020603040b09101b1e0203030714040302040c0c170c0d05 73
    0x10648511605d180c0d109034691180e54071030341c0b00246181886650f6520301113441d070203040d50368095030290b6400304500e80c00188030318404800c01c641c01800203001042c0412071100d02401c680441d0003035400660000751500605801c05002d807040c2c803080da5201c0c6140341807032030f480801440550003004000e500082c0710a10104403550b440d6001100380030004160f0b00c00c000750000c4c094001c0c8110300c1d071043c921910300002050540341100c0c1075840d1620156125002c1001c13000d2595a81d002009442d27040350b0250702e035070b1042e101070505901e4200101402c00d90240c5002c2e1584d02903501c0c07440302020140140c950405a076046540a4400e981984036401d2440c00e040891201d8903503140360800450282e01e00c491003080f144110f48642c9400c00a5203400c2c081480c4911700803025074010008100c0e603610841c88000c00828520383ca83c03e0030303200c0e40010140c0c0c040210440004001200e02c60610100800c400300c4610101a0f0500d00701409003465182c2c0c0310100300d0070070f000700802d60071440d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 953517266 1250 953516016 953516021
    0x12250e060702010e13090b250f02240603120702030a170f0304060902090601050a211103010807030501110717030604111c06060c021503070e0d03020a021f2001 70
    0x210a40100590203010388002c43d08001c00c06d50781d082e140c01b0015004900d42c610220404210045800980480035580c07000544103a520800708204500c2641031200041804100001c0012115058182c0c40e0a0039000c15140804559419107990300400400c4010380e00000c40307144140d0702c000040020700541c6064500350045504200b2000400000c000c1004001e074054a402442100c2c00b00c07036034984000458031401405070303000c00f01c2e0702110b410f5481400201d0304005c1001c030300340114414490b03425031409600300380c0c410200b9501401c818400c0100a002d07603210410360401d09400c02100c0c1e01c51100c4580320480300000c03040f000005c103850380c4842d00310044040e44240c0039503582604051642d600c4c1130103400b000020707140401c01700e0802d02c00d035848017001d900140035468a04624402414a5002818070340a005c0b5980001c1481e44074030b40390060042c013a401810214000c4d005002140042a1000045020008804490a4112419480d224003180380c0049014811440f02d00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 953518516 1250 953517266 953517287
    0x506010c020315061c11090405010b04020c060115020f06010b07060906020a18080d0207300807030210051009020d110f0d0b0603010605070b070c0812250e06070201 72
    0x415009500b0454102d20203031144074004c89064072035a811601207400010004201240286000301d912000b04107850603483c01600f15014070300019911222500050880e88060040007440d008000100310382c042380e094140c0c11081600103840d080602d218110749600d8140581e0106c00f9002c20740c6411f00000350311905100b07910080c219a03c0071000800f401030000c003c10b00c00d00c042902c40105030f0102c081900e01e00010650000c01c141400e1640d82c192404035078440380b5003a000c10722030a100c082c1841041204502031407480e50389075101d013802414201c01c2c0e031412144a052006101400305a0b80020003203038611080142c9a0000300342000c05001d40c0c0c4200140010301090720a001d41e40100185506a5148002c001090300403040c44080c2c00300344a001c0c0460402d00140b00451140b01d0010707408800c6140400d01d042050756a005203411103410007003401414401c03c90800314100700065044554030000c152882d4180c030040503460a41a1580102070208408046902031030f407612 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 953519766 1250 953518516 953518519
    0x111070504090303060819020306072604030e090c04060f08040f050d030203090c040612060b0619050d27031206170c0f10090302090612030c0f0c1c060506010c02 71
    0x842c0d40d4050500801402007801080340c00d010790b1510034003403e03842803e58031143e17002e4060003c075940c401c41951000c120406031201204101e000240001017a07840704d00c038034071949418002003445004d1001078200282800014801044140300ca41c2d0058224600d4004078a0156420382e500e290045422440306c000038031911070050341900854043e00614898000c48080f1a5510030f604204420b0781c2c410f204010701c403900342c40e011010031001d4002144464000e0700091500310030421401c2c4110004103500005100031079001d08400340c03802658012901031603100d40c0702528548803496030a0405004090024110710415400890b0300444c00034090410300c569000c564480d070580303c2d85034119080c0b1441c040003801660b481c1041c09511000100e650303015020342151700740903042c00080c00d403e41c050704844208590020410042c040c0b5410f54019060450b010420b1038500b034010200c80380b0802c91880310743d281d018182113070904143c200c0804511501c0c0d140042e41d06402165019 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 953521016 1250 953519766 953519771
    0x309060a050c1b0705130c0516020a1502010f200a0f0e0301090305070b090114041205041802190f121a030a0f210c080c010f021801090506090a050111070504 69
    0x110518140400d040044417001e45201c00f10288202041045a8170156083e0204105124001c0300809603144003828510103014440c1c0303281c44101d076060820341d080311140141c1d1500100120481d090280e800010140600c0300314215058002031241e0180782d0850003044903410101c85258450300014044013030140081101c05480e04004242c0e038410032003a01e10400000204031300d0b840c14403810a50030320142e100ac000c0d07110341d500c84244509580c3c60508128007800003240008485030101100344c03450342c0050f5101c07100e25940c50f03608440600e5400b40301403255809030712600040c1d2121140d61556001802869503007685084156004c4c0b041d80611603240d50381c0030003145582e0011038500840c5061520320304400b850310b01154203c051400220000c121400240340c0078044d10082103d04000b08500c18003480c032104a0304641e450301c1e40581c03400c1c8020800d5800928940143c4003d031101807038242a9404140c900340644500350400a4045c002c035610841232007000301400c03008006 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 953522266 1250 953521016 953521057
    0x32407121e0c180f030b0603070e01060c080c0d030e0d03052e080d02010e1903020a0201120f0504080a0905010903020906240c0606040b09090607030e0a0804030b010303140309060a050c 81
    0x1603444c2401c140012540452003401040f500e1500042c40011111031000d01e0b845603007055812103051213031580c2114200717814031126070407681c1406a281220b14940d0005aa0794021000900d00220f803448001411b20702424025a09450301d0324440e8582c4d134003005158059036400031144502643d0151030310b4000d11082800c0181c2c103410002c0d103500341d0b070f0840d8003210003144284040300300304100a0140c1d005040010041d4040c0101c903240c0710307007040001040d004114640080e11801c58040721503540c00507040703400540041d0130743e0241c003080c0303468102c850441d4041420450094286d81c418040e06684100d43c0d42c1141c0d401060300c00c1039000d00e84a0042e46c0c64103950350f4003601c40c244074a08000c0c010384a8104070810602c510425801040c00383c9a00c2c900390010010304400e540a402280030035000329090070000d100a510608020b0b12a61640c00d000340340180031034044001c42800c006002140c5070000f50640c0000100900043d207031250603110030300740b103140b0070b013009034410780b24 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 953523516 1250 953522266 953522279
    0x30c050d0f020a080105060406021015170604050d0e03060109021b070f09060509240a1e0e060102210c030d110d0f1107030806032407121e0c18 63
    0x343c9001c00c6103444c3c0e241266220300c1044410700030350240f0401a805a01f1132031204016400c05d0400342e52034407000358080e865000300000c40c0307985210180c682d40b041d000c1c0300c2008810048401c0303408591a284e80c095201c680000c1c0c9540040c81080c600c3c0d600464044145200c807821000081c4a0104441e0a103a4554043e007031802c0c14402c19000501d0004009524103060807601d1150764000d503048170b0b80f0310410599404181c408400fa400c502ca80d000441c40159440c00131240700381c0d80e281c08070b1003441e01c8685e05800200806860442d0440c24603000e0b60f21001c81c038140310343d00f4215855202c03c415403680f03240d40212000e400b001803c012520b500c0303c840d600140482880d002d8188461402d224401d400d840d0400c244003580c610070401200403a11504070160480002816a84100c619642c19890100556254000090381d40c3c240000550445a2540406c414010030310801c0043d0184405030303401400007520072500d0b100c502c0b00741803081003014075410385015049245a05c0c0c0a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 953524766 1250 953523516 953523521
    0xc01020a2003030f2701020301081006090603030219030302091302040303020c030703021f1e020606011115013503090307050420070503070b04110f100906030c050d0f 73
    0x1034450084000100211407110004000c032849851442a04481521102020728424001a40802924160104001002e0002c1c0000d50003410101c2c0102a404440c41031003048400c41e07842070071254600b10b0704000098010071800e00d01d000368550b0340603051450400f54044d02c910328070640e000b540d5503c1d444503000543c2c050b10a83c0d0080e42280c2c040c01081041c1035840b209404040e50010b4185d00d18010f0040c0c900500080c10b0b00780c030f05086160700604000310074440d04042c002c05600239100300702c101d59004c5004814200068020600c1d0751030031812000341041802100c0103c2d01200d45500112140d109113899000b04030402070210002c418056200d8001d030310468800c0c02340202c009114600b03405041640c400c0441c1c1c0d02c0f403c641c1201014500d5006000c12159400148003000102d01000500351045d8040c1c41c154120442c05820841130b550000e41a520034401400081c6240d07922030086070030307030b14941400100080521000da90a0150019104210f400c0c0905c009022403c1d8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 953526016 1250 953524766 953524787
    0x3130b03010312021506040c02070306020f0c161203031d060f091c121503140f010507050304030e0d02011e0e0418022b0209010303020105041403090f0607080c01020a 73
    0x3002c0311008000e483d0000c9072501660036800e501d804000021030044d180507401a15141c1d01401140c0721b02d0f64990b2040140d8000c8960701001ea00d0101c9d000c00414402d106014241007596070030a5454206441894a10000100602019542ea08441515210103034a000c1498010200e5905180c0300c6000e0396222000c90340d0b00c1180c01038912a0100458004039400e018106454141910f1566001c6030001d016142d0000c001503407505002003c40c4154442c00f1400a05030003801540d00000015400c1d10380162820301000360400c20003021a50002601c2c1d84004112403031a4003802034001212024121701c01240d02048146010340c04603005501c0c0b88205600f80c40c20b120030b51001c0c00c900703c88202c006029402500c2c4d0429501d031403403488102040c6a01d02d25031407034440b400d50082a000c0109810480c0580e560344140400d01c40c916120034207640d03010004500d00b031404001308070124080c034a12401520046150405c1011103429542d01e484d40800031501c0e0700342200014a0f6090f031 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 953527266 1250 953526016 953526023
    0x90f2904170d0e0310021c1104080c0307030807020d05011407030b01182601020d02071a0a1505060c0a02060d0501030b0901020c030301060c05030910032306130b0303130b030103 78
    0x4440b4104286409480040e50740100140984100010340c114400a9804000d401281e520035046501008145104003445000305003005902d403820410b00501e480399004c0010f100740e00150080001603171820880d4a020390643d0010030300940c0349820360141042c2d09541c0361140e1803004115800b1fa065101c1e03445000242e0701e1115014500070013500350005801500020340a078140b118203440740b0648071000c020b0020005207008030349860b410482e0081041100c10403000d00c00d20700c00c9200c2d0004c664200c2d507268002c003d103074030b42001c0c946d0184180c45543e00500e40403c46100581d000d00c4a0380b0b2160300034194030ba5900701100103000801003400202c0d400a09007001c51480c400500c00e40e42030780201801036185900b040c45c242c032045003014041b07506210800003505c0548a1a40c0c0400014498a000c41c409407800900c03104025181c0c42c5c040501002c408200c0740d6a5a50442c0020318a1003400050500d0103401090651080000c8850302c45c20f20000000e00c8480c200096040703a00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 953528516 1250 953527266 953527273
    0x5030a0c0905090705070c12080a0e0f1011030909010b0915070803130f080d050f0619140409020907020c04140105030604030e241801090f290417 64
    0x1403410095035804650b000e2181c0001001001680d482d00560040c41c81c50300807080550042c1e03a03504000d03051881d00808440200b401300d44080116000361401200b0b1504840c5c200051749001d001c940c042c19002404010460a010040e01c045028011500030a0004e03080c2c562541e143d5100710410303800050b4240c02384a69007202c00e10601c001c410740f14880da0140300c2600d141c441e40550018542c0c0c049043c4c4041040034006c500140c1c80c00c1c010300315040c0e1030502291901c0c1c42081a503294100a107594010008980c11205919401c0c94100c1a01e558003000c1d00115000c402040c010208507400030f40100521051100c810f80016688481d55400c54081c00403a00b001101c010300c2100b0300c551501507010b0400304002034082c4031020b000400241c208410400170302c0346080c10418194100c0a118400101c9c8004095081402100c100c02800d155224525203d258400760705988185411108049162104051303410783da680d6041d0806070054540c1d0702e844402d0344070000960449110b11 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 953529766 1250 953528516 953528531
    0xa1b14040c120e0c090604150b070c09180501111321080f03010f050109050d0f0f05060a140f0403090e0c0c0d050d0f0c0905010c05070807260309030a1e05070605030a 73
    0x1d024000d6044880721410001c0d50127103000380c0742200760000e000c11100240d1050740403802d002140f0945d2012550300c034001101d4115402d00c07600312044200c0c0707108500c6041007101900304082c1400000c440032900f40f1004003000d0700800c64900c014500003000b0700800225605400c250b003000d14181d42401c40b070071218580c3c0710019501c1c0d80140c030a20744c0049403201d402d00418003880b984014076001e251108041035440d518603007085421117507041c040e80c0c2e944d40f035440d0103041545203611500480000d00141841c0d10302801c4000a80305205805070080d0004407144003840c01d0750700030301910080b02e50202010030080c10542180070002240c40c070f0804a21a01c900320f000d0b0700d83c622a2a11504021418800111040c49105905076024407518200045000c0308200b120002d050a5160700300300030f90b2441480c0000500d512502c0c055009004010031aa40410b070403502ca0f500c4140351100c020054090488401c00030006480d0b4002d8940000700740360048021882002c95003010002c41 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 953531016 1250 953529766 953529769
    0xa0c120f12051612090c03061d0a08032d011d1609090f0b030a120f0810050105090d14011a03150105090402210a1b14040c120e0c0906 59
    0xb0342c012204000c0c40e20310701c8407040c0c2d09401400b06102d140c80204010441e50043c0e10307894403d84169104036040c45c0d0312076100401020352604540540030000c050106141079485610032400060715075542601e154000c03c4100b203040200100c42c1c081101740300419a590001c100461244607400d00034411800c00017200b160000041c52240c4020b44c4030503007514100003100b0003d09806400c0b03503c16540703000c0004941d03020072403180c7c0c0d14410b843c0890346c2d0703170602d4000700340354848031050040c0074181c0188803480242040d00001d8a80a182c95901ca8a0860014000040c0d10b84c01520882503001c2040300302806411100342110b45400e05031400a521062560302d024460b4003001c2c0c03039440801801146003110307180380c00c24002041c405060081103007598000c0c0c80601e41c0c0c20560322a2508904014624400d10a64841e00300900012032514501000302180ca01c400752080d603171140c02c441890300410034102c03c40c02442c0c04200c0d01184611280d99050242c03102031045d000070700066050b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 953532266 1250 953531016 953531021
    0xc050d02010203030a0f02042d0b030c0406110a020616050628050604090209091e03030c0304020f1f091d090703120309080711090609040b0c0a0c120f12 67
    0x65035810390007585141d45408030800101030791142902401d03001c0000203216031403000c0c0a40913051800c0103030035100603030041c04640910b640c00601c0c030590038000c04c64020b0103082a10200d901d1401d00d2418001c1e02300413a4101001244020343c010300228a91031004681700b1480802403040d000c562440d110040c40c1c5101154122110380c440b08a1040703a440764006811064100340040c10214000c402580040d0121a0481d601501540180b0004510b809423044046030a260304000e140f442c1844040107407140b000501c00b078020500c0c0c8203400c1c8a07441d4003e41a03021003032040c01d40e0103949a03600040104040c0c2c442c501c0d105d940070b50f0400050301c9000005016001203402000c03d5440c42e501e6900d511070440c0450141981d50350b030302c2e020841d10703401414001c0c41203000100d024034100c00c00020740c01c050300090240c050310341000000b40507000b44d2600802004001500c6003000d110889042e1030b2007a008200b00c00c2d885129020640009280cc00b4180c1a101c18102c1154002075004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 953533516 1250 953532266 953532289
    0xc3b0712050c1602010207050301090b09100606020d0302030c09090a1e180311070308030901061d1311370501080415050415090c060201050108070b071407081203040c05 74
    0x4200f00720201d216064200d840d42c0007441030040c2c03102160b440b0000390849020201c10788908014a04028140006118544c20400208810030031681031003402951108642200f000345a40040800c00c031007d410107a0741040d4004224007804c1c541050141e01810340141f0a0b12001c0d00001110300d4481c10b409161303000b221034100902c00c22295241241d0442c21541f003001c007030107107102c0800840c803180015031040840c00004a04d051401c07841144442c8804a8241c41e0680101800075203284003060303900c00c82e044545406035510020000e41120342c41e4138170f43c0605045c3c92801000c00c1000c101ca07101c0070b01c1a402e02c2904c0ba5504015101281c4c111801010f441274100301e019107100540c0001e0b00036004494800b00d400002250001301c4010324002e680c2601c0d0382c40c0402021354240074042c00f62490501518000e40341c01c980c0c400318054080010600c4041040420f90600308000700c1e0000c0480f101200c481041030002d50303880307a0040c0c0303043e1400b074042c2d080071489061108010a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 953534766 1250 953533516 953533531
    0x501061e080a0f030509060d061401030e0d0e0a0b070302060f0901020a0207090203040807021507050f2d010f050112111804080c0c3601030c3b071205 66
    0x1030b034016250303290b01e0215850801203080c04001e0101d10026140e12000d0806808540000521241000c81c0240d208403e814040d04043c14210100d036101004150016102d5644c03c14110784c100030000151040001d07000000d04820200b03c030410b05030300044590050380d03840e845508540740da03002c1c50300741d118034620031003da030103100c04110100d40d1707900443d4400e020f61256800c10700d2544c0055100c005407008000b040c200400c002060000500003040841c41c507a0040c29282c140390300031144c00444040d2100d03d001401d84510300c03450203400500390240303410700c20040740d0785514038503030040503a05059a005004030070101c1c4c2420030710b015698078505255100716541d619521202c4a500590701c66907103001d02c45000c00300361038114400c1140d0503021161152843c6411007468207401c110b00c81c146082a9074010004602d20818007001c0d10841454170310701c0f40c050740c42c20003d50640d0904403400c2071900c1004043c10361440c003440c0100c0c016600c1c0181c5020341c1404000b0349105032000e1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 953536016 1250 953534766 953534773
    0x31b010b0a050d06060504020f030f090f1f060e01090c0212040806060913052a091605030405030c030409091106090a14031f0c020d0807080f0c070f0501061e08 70
    0xa100525040d543c1c080c400e44144030100d600b50b20740b40800c6c01da0300860b20595880b000401070180544442100a600c0440c1a0040031070501070201142d582c112005038860220003950355201307a80c055003001c2d009c7c00c901d60040080f0b5a6414000c4024200600c0c04801030003001809907101d51a142158111410100240a5a1101d5080260050300036002c10030001465400c0c000007003060001d01200030608001e1000f44840d141d49429608064034282d100302c03804002c001c442030004180410302203807450043d480e0380c1e40380b43ca00e1840c170402800c144035100109000034003020540009100900c036072010284500d1040500ca00c0f801900f86c225480f180042c418841442ea08024a01d40c0d10018100c600364244001050040015460070040880d200ca803c001929010044031021942c5450442454034050000174030b901d00c064080c20319068803401082c28204610b0907901200d030004844c1c0740c800003e14006008224a100742d0340d05840d05c1100401070140c802402c0c017100d0040c4060b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 953537266 1250 953536016 953536019
    0x301030308070e0d06090c1802070b0a092a090f02120a11130e09190b070f1e02030c0706210504050109080301121728120e031b010b0a 59
    0x1540d03903000d42c0885a1300b00540c804a580858994056100d1180c0110301002c0082d081520400c00700300441409442ca81c0108034540004880c0c0648a6108580031070000c0c0ca40007529002c0301091402640039601c6407442c13401d0003403259003c0d0301c0c0308a45101c0790030400c40d40c0e0b042040c004d0740202226442c0455200c1d00144a14000d41c022421451075880d24a1400014900e4882003084a030041103010010008102c41007108115103114030b901284501e1118410391348070140c2400081100d030811800b1082003044501903039121116039400c20060601020201d0029a690006807846215100b1f0301c000081290148010b004041d10550f240511f400b0440c1c2d94801524001d042110300759600d0f508400031a940d0380242d4060070185217444508029418001d6085d042d840c8140c91103882003240c401c42100b00c107008150f118000350122103003084c80030181c1f07444900a5480100905003012001d0100001c4024000d0440a00074003e088046075052401c94003c2d400550b088120a06c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 953538516 1250 953537266 953537281
    0x6031424060d030f02121303030215091e010e01020403080a0f181e051003151413090f060f150b190e1314010f140a031202010209041b0e060301030308 66
    0x2201400480c2e50045446c40a258860119240d102441c050100b20300c0c04400d104040d814000a04e2464110700110f0710750071706181051f02d0b61560032081c6503551009081450504081d00b24441e01c115100085440e41c1e540e00b00300c2c030f40360311440701c0e107000030340160038804401c0c0540c03520b400c0e5a15844030300c143c26062440e1481000f081444108011801a40c0000d16503516800000416a107030f4000c00c078001445111440c1c0e41440d00301603800310b101400c60f039607a120f071070a4038894a143c0502051503d0369092001c6842020000074220600300305c404c418000441d003080e042080c01106201400c1c0d5118002e40c250b0280d200120003510302c01400c1d11003e0300c10280650240401003c034500b00b403851210310115110760206d0100c0c00c68090040041d03c1a00941c50014091010004170900341d24001409044803400000c00f900380e02040d41900500c00d42c10350356501c02c050400c01c807030203400072015000d40b03401c0a440000354011403015000e00707124040c0c9048a6254440c2886a2506030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 953539766 1250 953538516 953538527
    0xa0207030b090a0204050907060f08090c0d030c020303121501050705030d0f1409071d04120f0201022101090501151704031b061a03120f0d06031424060d03 68
    0x90a800080c0f003203030700c5103001da40d6500c102802802c2d0724000305011460000e014020300c80c0da00c60481031140d003404000200002081680859030210f81c2461b030941c9a2400303540e00014040040d40500c4003040c00d507020709401004d50301030241c5003800740441c5010001195144038007036004003550018070003d0541300d0a500807400c0446054004101c0200c3c40e01000040394013150752006590020300100060324800b60002e00c0c40400207e460b00501d0a625600e14801912640d00104101c806800d140c06100b0342c1652405620361315081101c070030f071000c10074100c00d0a0080349182132800c0000200550500c844242005c41901c1d86c40000032941c0c0c9031228044004c200f030302448424003e821807444e0107103c16040c148181c0000940e00203600c211740c0310319680f08182d40280e0040c0000742200c0ba4450654403812074401c000e69948207038454200140c03886600081242e840b0480b001032102021916a585040c4070b050642514840450301d000ba013802d88130150003904e40c4040402007071150 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 953541016 1250 953539766 953539771
    0x14070c0803180a030507140c060708130b040b0405040501080a26074809200708040501080703060f09020a020f100e0f010510051011030f0306150a0207030b 68
    0x41c48142d0b007202030300004038205101010f044000410000b5030404001c405a02c8030500c3d00c1e4440100703998051403010134428420144094048507021480031441d0881c640b440d005400366203551500d4940e210700c0440c00e034002c0c0c01401e00c03a5040200220f1943c00001d81c0d841096001043d505900301d20480e024207882d44042070341840c00d420829400445c0c003a8000c440c43c5285607503501210517000e1a020000402121200110801b41c0342c0c070968003204040b080140e986058000508000d4400c50009074041d00c2040c3d0710301407001c0b035048103100a18010700b080f11820f0320340001d0b513030b5400003c60449040b070040e408454880c510500c188003040d07024001c0201030380105c4032020301c201c002c079180c083c5000584c5000342e107582070000291020b1040c180903090301d2000341321318180f0101d90140350405015643c0100d0282c100c501d12280301e034110300d91400c03180041d40d07901c0800481086e41030f8421254507000c0c0440201c1c1034811400c0c4811900d05840c10760107402064115071b158000307013202 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 953542266 1250 953541016 953541031
    0x440f0a02030706050f04170c0a060c200a030201062702030402040603022d01031107060b01020a0b090d02120f070b06010e150c1c09030b060411030c0c0114070c0803 72
    0x40c002e200000c0c800d4800e440c01500e40707840075680d42c5814503210180140003101a10419400d012840c0c1d0300034005110b01400e6880b81d07020403440c403144400c83d039101c2400d0b50072901621840e116024101e02040010182c0c6c080c3d4024080c3ca61510342030008110040e4402c10345a903680ca08018503180da5001c0c42e0414402000071903000c0d0780350001f4044000303400c8080b2040d080c107aa404c84c11206200607001040f000e0038180030700c20040522800c24010001c02070305280d1038401d42c114681c402c0c8412042198003c151616600344a00d0302a03031080b080c242c1d4400b5116601304400349980000984500b1401d94010600e0440150b0700d05c2c0340440080c100c541800110307184440d050741c5c0c0c0d580c2d120301c0994a403040ea8486001c102001c0c508552030700f80d0040e21021320000c00941790300407804010740350801a80d0748a1b4542e40c002c00e004209a07208004c2c600747c0170080c080c4c6107103500c0040a402c0a9a002400360600480030b69180610503240c600100303002e40d0003040000e48200c083c55109e681d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 953543516 1250 953542266 953542273
    0x6040206070f08120a021201150c0b0414060c040f12020a0b09010e0307080c0f0f240f07030801061707092733141c440f0a02 55
    0x9010b507029061300b43c203a4402020503000b290340505140500180d074014031b10300c080ca4090062000d00982480c0c004030300504440c3c100d400007420300000044c100848a00401181c105250201705030340b050304240509404812005c60020fa0345990307159206090713800510304000d0a1800d58203c0301588030340c0215040c440039018010b03e40e542407244400521310400503002075108401040708007800c1060840c03051040b1014841203440761582050140c841d24003540d042c2d280081204264010152211003002000852508050f4031050f028106c903c1c903191846841c6241070082c06107441140d03585c00003124078608000c1c21900164062065507040c0456200308000e141840607900500e07110000703114002c90317581400c4044800030300144001c40514440e02c0c10302c00d448541c403c5d00840f103881407441130482026074403400d00a031902640032850700c034a00c40500c084424142c2000004501c504007204d0349458401642e00002c188803440172007032404030608480600d40d0050b1042404500c03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 953544766 1250 953543516 953543527
    0xf0b0406140d0b1f09080f0d140d021804050a1a090601140d0b0a0512030307050702010e030d0305040302060907030b0609100b0a0c020f011b0311010f0609021b06040206070f08 77
    0x1141e100d6070b20a1410604100f82a907000c4444c050401100342d44181c486500c10700c201851408049500524488186400785046484025101007405840305500e1050b01c00111213245a80044d409041751300165000d1003590342d242c481a048409259410a03040d0301c40750000500d24195003e540e002c23005050902008080c2882851640c20403100891046d907104070140c41131a01070002002010115480942c112642546903100d020181c104018881c003c01e14100310380c000c400d90848044050100c03007001303541000041c00ba2009a0f01540940101004203024420210f03000054907004400e4011035202c7c90144042454002d140d260304080e010004940c6565420050100b00200d55544140c1d003000d0041240c140c821018160602c90624180384140e2010540440c00c40d80500701100f0b010340e000c1e0f81c01c3c007501800000e12081c2d89420000701b403582c500e90103040e560781c0110120361540b81e0202040d940f04020b84000c1d51082c000d10101000592060704460154400c100c0c060400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 953546016 1250 953544766 953544769
    0x71e03020102250212030c0a03120b1c030314100303110307050f0a0b01120b0f100305010e030409060b03061f110604150f0b01080106030b030a0203030d02040f0b0406140d0b 76
    0x403240c800f020361418000020b4030541c9881404905032070304200146142600c03a402c0e5a03031f120700f200801403c0c0280034020040d03610b8280d001200d040780113031035805e040124112400026080b02c1c4214042490145800404804c00c1c401c1d40c0b04081164800840d40c0c150b0324203443c40c141c085011a1140700811150002410620144011206400080500c403000345451590780005030080c07030210354044000700c00300d4203c00c2200e8000d40d0240304641107844d07050b503601141342540c00185c6190b0804140c005035040003c0200704440f911281044069190000c2e01500d22040e0303a8194060308103140c007504c0200c030700d5040c11210001c3c2026142c0c07007501441e5504014084401780c8550741182c0035040c03100b2150040c2c5d907104524060401c102480000042c080d10310601840c2d0403d075640a0010960701c0810001042c0c0d50010103c90320351840e03c800201950050003541450300e90a1400078010701c4450940e001e88003540c407540c51901c00c42c5460b40da1500809a019600c0c0d0704c454052185 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 953547266 1250 953546016 953546047
    0x41a070503071e0e0402220e24031e1525140d0209180a142a0a0c05100b040c02070605040905100b0304060905010b0a0803030c07060e03040b13050105071e03020102 72
    0x20301080034416450700d04042c009604440d102121514a084600c9078a0702b0b50f0007140d06041162520303200c840056460410f18540081c00c1031051081000e81c0502c404502c80740448115803083c041401d000c0c0c0461802114040c00506504d100c6820502000079002030503000303041e00140c0588146102d0b00e00350680c4000d120140c0d003101107596150840c1d0b00c003640102d03145a0003400c142402c0ca003256003a8100780ca0f031a84d03402001241201140c100c42c00d51180e60200d1403690048100c4807152003a085510040101c20302261107540703002c070551440360011802c201141c0154a07558102860031603010040c102c010403034403c02000903400b0424002e58005180180e00508000608500500c0c2c05401c41d0080300c40b403482100040410000c038400002242d502c000b0841c2c10b551a080580b0381a4080c0540080000483c0030116001c1307a500300b06800303010502c80380c02c1c483c00001da0321401500e1500c00d40d2406042c00302c1324120340b0030b400c0a440c0c5508009110b480018982060310441300d0300d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 953548516 1250 953547266 953547269
    0xc0706030c0201180231140f1f0918020a03030215060f0a030311160303020a0521250c12020315010b070b041a070503071e0e040222 58
    0x200340c0c0e9070100c02205509201301900c0890102c0d180b40c1555242c0c000403088200c2680700c1310301d01000b80218200d0400008002d054400200f406c0c02a01e414400c440ea00703240468601202c9004c01000961042c43c3c16401000c1c80c141030303d04401c86c0c1c200981e01d4080e014680340d05021f02d43c03010140006841e210b564a00540c003e6028160030740c50100707124540711018188900c9101480101c03503881c0d440c0a20101225890300300070040528880364075040000b424401884612000d10001c14140c0104100722424400c20640d502004c08000a00e03111456800032100b684092004840301c44911211103100018184c0082501809540740b00c402c00780340d008800c00380b20488241d411410204142200030f0003c0054001941c1054a800014050f030840940b4260010010a040c8071403410721407a10920300c4d50020061501c2c180191840e4008d940c0d100008001c6110308086206a01d541c0d41031800641d94070741c0a008260402020350440114919000c0505600e00c40c2c02220107603100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 953549766 1250 953548516 953548529
    0x42c070f030506010f0f0309030c171207030e0615011e111005060f090414010203041a130213020c0c0d291b0a03140f100b120c0f0c07 59
    0x48140099040c02400e40d1005003480741400380c940c405076081a00000c0c415055000351074000703490621800d08580310b140c0d190303014080c0c18a00100403039021800008046900100c0c4a0f0b500b0350f1030b0031104604407803c000780b0808640256002c100f04458080600e101841c0501d04420b80d82c00724030000c2680c40800159070046941100c8140c0340440c1800007040c101403040e000c21452a0110204840200320320b0703c1813207080c0340c1000604204084880381240141400215100d10340b9142c80d20100083c421060814160000016446015201c0088103030b40d01030b1000400e461281e48035400b94008042c2c903032403405410740b14419038581d50740310354041d4000d0f06100084220134000700d48044820b4844c6072101104410048040241c903000800405030707203900d42d41e0300e07a601e1044005103a40c160524018111101340301004088250490042100340c10305040580d0741d9081d06041d108003180c40c3d11110b503410010b454034005201400c00c2042030a40a4a0141c4031010142044455000368 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 953551016 1250 953549766 953549777
    0x90f0b0909060105031911060d1d0106050a0f060f0e030304120f02100f050f090102160e0910020a02190501060e01060206070f0c0c09022b0e0c15042c07 67
    0x40085140403c0450002100000441c59040098440100e0068641f00c245c0c000d04000446000f0380105030701103151244480c40012602c114800401e002e041548202e030321801e0104000b060081644000c4002c41d00300f41c0b68684a80407240c4280c81d00c2c060042d0303103545400140400070790308110180c554000c1e48039a018003501c121520410521400d001c2e150020440244000098190817604036031400300c280700d0301500d901120780100e240040f01508040d400100350310011303411a118950501824462043d241100d5214040008074081c1281400050740100c50145401011007000c0410074041c00000c03510980303c01c404011018280c0c4800d005a10038030800540a612040694030300030340d480c0c6040c4803034042d21201d440003024010141d000da4001107445c26560482c04100710034450303a0981d001c44901840c2040204041090918903010352a9a50240d00d0b10381d40b50094003005811071401d04c2e003402900351550400d041d203400065846c3c5003d046d5400004400c0788170300e0040d52807 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 953552266 1250 953551016 953551019
    0x9021309140115170f0d080603010f0c1407170a0c0507210213020c011d01060803031311060c0132130305030c07140109020418050304090f0b09090601 66
    0x89801c1c444000c02581e4980303160096800811034070b080840d8901e02d04016692412407290b8101020798800342d0320f034410001014141034015106a1040300200d0080000911a609070fa05aa542010038000550713800d8500c0c08610090020b010450302661409119000d401d0703200c0e10130384c0b11600201c04190300400c400c0c100101081003802803c6041c007900c0c03241800c10398440f5542c040680082c030550b001c6078558003218165041c1c84000c18640d00901c07148806105510400303042d400131802650a0030008565410000201c1e07004482456030040d064500ea240c0d180010260101c043d0300850401070340e8000070342406208c10204000c611401003c42106040c80343e00207401e2044070302c0120104001d0008c455412420ba0300d501070900702e40d42d42e151002c119107441480e20041c00c036040c0c0006080020070540c443c0d40501e01c00d650801c00041e540d4666a609c648540b8000c10340d41c0108000d0102c541190844095410900350200d024015117000a8030040e088400b0b942d035a111000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 953553516 1250 953552266 953552273
    0x504120f110625060906091506060e09180309090408031f0620070506040801060e0f01120f0c0e040501050a0b0f06040302010e06130807090c0201020a0909090609021309 74
    0xc41140760002114420300d4007489054075822500c000070000d81c46034000b6024401d022480d00801c0340c01d0b52210040203000d4543c1340817203d42c0b0300c50301555032a0b45000d2010400c54020303602039940003401001c40d00203a44480030041c06c18201064411540014441d002c41503d8070403610f030083e40f00d0100302d500c0f840c0c20310707040c002281044400504004450720400910b60844040f00c071000410303194414116845d100799103440c1103a84901c0e00402c0c005000105c00e0303010340c0010180c3d00074000303425a03074071401d8082d00885000c0c000c0008502d0140314410000f0190360040c15814415100c10845030303646c140302c03244d2074811641640d0070b0351220f0800c20400542cbc4034904030303602c0440d0703030f8040000420702003680d80c001c900009041c445040030100090382c2d40401e48020100c0089001e8040e034448210704d403954a0307889a00c0231907091580c12484580103001b52208440c281c0d6541781d0f00d80ca4050b851000e006085400d03075410303642e0300c0c0d1040980c9a07064104412403c0800200f502a06480c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 953554766 1250 953553516 953553533
    0xe0c03090c0d0b0c09180a0b0306061e12070f0314160b0417010209091f1a070b0c0918070f17010e06130504240218040203070504120f 59
    0x80898420901c1c0d0142d080043c150781c840e9500030140034640c9840d01c8081d8040b50b90b808200b40d4400402040008000341030356290051030010f80e0a40540b581515608203000000035000710941c09181200c40d99501030804241998070b411140048a140300e541c0c046000c000b2105801c242c84c04e5040540600444400b0407100c2c60100014020484080c0340c01040c0d074443c00343c2d006810212160502007a0888001d40581e88448030040c40c40c001401e001c004040018001e030040600b40704544070000300481d4610450b01c03140640000305142555641c1c038000f40030383c02091400c0e0038000b0f0100107456162582c98541e8030300da80c43c4400c65402e110b1009041d80c1c0318800c6034030401c2201c070b1211400b0802c44904a0440700343d4128840ea91b210a00054201c2000000034070070f0350b207420204014012003880789001d001021052000294185004006078071844100b600110030f031740074401c0c0c181070550066a0001043c42d010342410b484808884d101041200103580894000204005011880 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 953556016 1250 953554766 953554783
    0xc020a1205130b0a0c03050a030605271e0a0b12030d0606230405040b030120130608040506041205130e0906090a0f0b040201050904020a08070e010906020c09100e0c0309 74
    0xd40c48181407203080718001300746645d41600101000000309142010900a030060006010000c009800c10b002d030580e0180c0c00100034440120001e8079102007542d81d201200911040820500c8122050f0b807920310160290407002050394100420b0301c501d6101400a101600c030010710303044040b07442c83c60210b000b000d2018844e0f001600b4003080d0001c44640b003941d011281211020350b00890184081700001e801024074401d00391400d100004008002171080b0000d051001d142c590380d280240d11410201d0300d056007110300400a62014000c1004200304298682d540b08003440c0542c9010040b911001c038a0144e40e0080c1c00041000c0d05015052105111061340440c0310b100801114000e40c41e004000011540090504001d03c0e02280079644964111080600301420640d51226081002041c00104940600000d01003101908240d07115815400845085900819001c40c4401c2004000305020300072003e110741040c00006c42400d0008814481da08110304c40d500c070f03d4035500c000d0820703004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 953557266 1250 953556016 953556029
    0x60303030209040b013204050402070c15030b280b160201021c02341d07080c0409020d0e10061503020f0313020f030a06021e18040c020a120513 63
    0x1007101ca1b000c0e55451840c070348040f41d01c0d18603004100b41c810514080d140324035080030340c200d400040c40c4809c1c031252060300b600b220b02029070242e19180c8070b80204d0403900c0b907008045e40302d5001740c0701a46d40111404a6503102040b050035000e007954a03c401c0d03100d41c1c04041c0001c83c021b18000000150b43e0144140d81440c1180450300c00701581c038445c001c0d00c9840200c00c40d51070386916885031840708142900140024100d80550100d180c4402a010340c91105450081c2c02117241c0c40050b4812340304521a600406801d8030403403e2500f0400080042e4021130039403219590380c0d50800000c8030082016458034200b1031400034030740b820325440c1d1b00a1060001c1301c20034140104810305000006008880c0e1102c0b558110f0000151507200041454030b030821502c0e454072426816205025060b80140211803a4400d8019001f103512400020703809018000074039102203046900075400c042d0010300715000300d441981d42014880d0b40740d020a0888a003e0301c00140042100000c4c00c40c01140300340078000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 953558516 1250 953557266 953557277
    0x91202132a020f0c2707090312020307050a170d060f0f05060703020a03080c0c010903020f0705010e0d121b03021c050306091b19020f010606080702062206060303030209040b01 77
    0x201d42c0780c20381c0d071030b4121a040c0d4001c0d08007074211442100303421141700d040d0400505400050406c4100182030390100c1c04191a144000c00d0b20154003400082150038a917030000c050082e012850310340ca000028040c040388081202081041c0d0210030902c100800f52210701d00d51a945800c00c9480c41c01004c043d0086070046104105d94800300c1c1e00085c00300541a418a08024695115014007480703000da00f6645030207600700000f85041540114019041e29034600440f0210f81e03a807801100c450094503045c0e50050700000c1450042a40342180d00f08030001401c04003c0344441d8004c03c4020016180150010780014220125401d000710902114901c1850102c0c110309048000a03800030020b0b00044400240400c0154104c4280c000e4910b02e002000768070503581c400800c040c0d2146100c515140c029445c04401250349030207800038074050300569004020301d644400b075100c1810b5041d26076011001500c1000d4000990324003600c0080c42c407a0750096110606a002d205c10f0f141e00300302a070306020 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 953559766 1250 953558516 953558533
    0x807060306030b041b1a09030c010f0c06110c030a090f0504020f032a0313051905070501050d0605060d060e06030703020906060a230912030307091202132a02 69
    0x7548809541d0f04181c200d25a0140841c0c40d0320302c25545c400c5640030301c91040b0700105144031811140c01510920500f42c05807910340d071100c0011507600043c24a00c8010030f03242d401e40c40100b1001c4c1c0c40300000e0b418415039985030004103075125141d0b802010440c3c0002d0f00b82d0600380900303c101e040c0b100080009480550420944482e198424000241480d0310104400082034041c001994084102e1600150b4580d80e82071440c50085c1101e0b040d034046d100c601c41e4030041d80315126100c6840e191160060017810004c1d00300001115075a00c42001f2840f4039032104804901030751803000a0803030b1004100d00003a61480c052012910120040a080c480d402102d0200050b88400c0d44980e400740c41100c9990381d451001c042035541e0303000000360000092080400c034003524070141c02407651600448524400c050040c0645649201c01c8403c00300240010001f0010207080800101680f4401040801e200c00004101d50848840314464542d0403881d01101d21103415880c401c0f47c401103640301900804 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 953561016 1250 953559766 953559773
    0x70b030115231611130b03010b03120414060f181c0b0613150803040303020105221e1a060f0415140a030b0901020703080106091d0711010903020304080706030603 71
    0x1030045003064441020303100d0f20842082400c1900c07030400c141c0145602000e100c110540f00091140150365400b13903181000d05a001c0c9000a5442d010580d200c10040c0303000d080c044007408500d88c004500d9040300e41405030009a41145000d414025583c0b80e1080300468114104211a81e42402c1c050010401840c5c00c1c012410010160340e21160070303103020924140d000380c108010b25440c000c901810704013507408a084000400207000301c0380a07500034000e03034440c0002d404a0105400c9190144109008481c00161014a050100c81d40c034100744030044405031100c504015449a16400b080e040e0f004005503490f05009889502005460030019004118464004010107000d040040c104c80c40c441e05150380c0c0d607441d540c00780d0307480080041641000c06e6054043d401c40d40c1d00303d01150700180085540c900c60510001101c445140082410b001c503035414a0b00d4101804d40010028a40d0003071402d110b0034000e801006100781d00942c0d845180c0104181400803540000e81018103003002007010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 953562266 1250 953561016 953561087
    0xa0c150911090f071404050d06090b1b0d1e05070c35311415040b0d0e012d11030105060a0509040c090810090b07030c02070b030115 58
    0x10f554284902020785e203501c03041e1140517a03070000754051b201045100401109421400010380f04600401f550b480340040111090201200014580c20034071900c0c6a101a03a0800b412929003540410101340230514844141d800c1203d0600100c0d6108280500b002040b840c8122112099a486880c4400703e920a4002d5010341904843c21040840c1003c007082301d42c8020f84202c0f54400003050121074045136004090321038400d9403144644d42c03800c9082424407219480310b070803c44031618a410301b000b010342000e400400e003400c080b50382c03507034141c00c0814248100a00e0780141c0800c5402c0104662042d0700887d074000e1140742490502144402144036030040d1b0b03041d00c408561041d101c100d451320444050141800081d41305081121891040c1d8000c2e018006030b078000410740d4258600351100c001a41d40301035005005011400c0040c0d02144254080410800a4415505d183d41d444800d103186070400e0b00302d00c0e115000100356107546a00f096452a80d80500100c0c0070a40507181c2041c810f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 953563516 1250 953562266 953562271
    0x130302030307200d03061802070804180e060a1e020909130302150f010f120b06010e0a050a0b03060406050108040507030f11030f0109140a0f080a0c150911090f 70
    0x83c032041d081c203950642c18007580d800c05400f560701120b03004008044000c002e00344c244a81d000e0310000c200740b0300c00d074003940c021141c0c181e0300705045620346803070550480c4a00d0114544400c0d201e070343d00d1840500b06003c0c08094060001440040380c81219074000c980c03d02e486103544014503104100f140980c0d214542c0c02c1764031000c0c2c902c401d080c180300760400b64140b20b8803280004080d2907a504104c3c405150001e00f9051b07481465150304107580b517038091106810083c1018101c034006070001100c07036201f070030a10700c05040070301000081556000450108085600000c0300e04002104121050825214040c0106024030700aa5942040e032a07150301c2e450540401341c00c035078402580400388011400130142d003140c0502125028142c00c00c0041c020503903000704660805c0030140c40c0c48503200029206055941100da03014004000d562450502d80c0101e04042c1070190300404240420f19031854240e080103055004103401c00c007450124000903040c146c092140303440d103060109110200c000d299 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 953564766 1250 953563516 953563531
    0x3070e21211c0f020c03072427031101021602040e062a0912030901022506050c07031a0f0705040b030604050901090c0b0703090909080a140403061803081303020303 72
    0x2d400d070f042c445200d01a2080120f040698800000c0c80e000b0041610602503000c03065159040007000580c11000585036810140100d031108481040700000a400d50440100c0c40703410306c4115000310801c15404c1e030300b141c119041082001d4100c42c05500309070040d0140a418031002d0280c41c500640d03c51912411310702108010312070180742070070032842c180803105e003090010700c3c035010141d000e00315990701d0340402003281c010700800000b441d148500d980600c1107250040d4a065001c0d00740642101c80780c004000d140e44500c504040000850000300c00b0031082e501c80d1000b41d5552402150a1548140c00b0b81a08104203003000304011804c222410b480d0401400c643c00b140c0d035220031311a1405400c4214001e0030303855001c2e0300028282c0400d001807000c640309442c0c50182e5540c0c0d84007501101c02c110340203001d1003410424541614802c3c05800501c154428807075050681b0781c1c8800f011500340d0039101c1c0e07582410030303860740038150415030700f6070710092118a500d150350055400075140d010181801 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 953566016 1250 953564766 953564771
    0x1101050c04060f0818011815060f05011b060c03020901140c150414060702060610030e070b030c22050f030109020d020f040905061003020f030f0303070e21211c 70
    0x69805c4da0b0070280d068444008400070b0000759800c02484005601030a01121601130345d031170f802130705225401307040101c0d500074030b5085000c2e00d45801500e001c0404a81003400c150090b164000040052040c0c03031840d00c05650050f1a000c1e41c00004d4005140110048808c0e03505001300c0c180341000140c5842b0402c0030105105081c1c48920f80104000c0210304807250364041d40d000c02141c0e56002030f1040c07040c00121009106408200006e40455044040b1103591383c0100c80144151340000b0019a044540c0c8242a4035150f44414000c03040b61070013920b01c804c10401d040401041c54460152000c0c3e030302c120002c01c0501030990011786450140e5800a010340d066000418031a40c6607417240d004250072105540300c1c0d1422007807039070403602d0901080b4400c1e004e9903815041c0341400a1810840803c150046155448005c0d058420609501c54150b00c000c00400e0640542e144c0b0841c1030203030202f04020a03074500c003810700d80007000d80b80341040315002c824041c07821280b01c0803031140c58010104400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 953567266 1250 953566016 953566021
    0x1b0311150f07030e060c101104030203030d0b01050405120c01180806040f050c04060311040e0106061403130c030515011a040506030a09020a03120806030c0604141f1101050c04060f08 80
    0xd131508400b000780036601c56008124184020b80c0803881900c01c0c0d040c01d20421640c80200d400b424640200c0c000650994130034032840181c4107840e884080c0c0301005041c158200f91f66440026101c6c0e1112946050300e4001c14000e610325600100c0b00851143c0c000103010310141030031051036503514010405401d07640404018400d0000034404211038280140062000e00e880e030038114034240c1300c419a1030140b072401c0559010301c0d50600c122820380d101c59491070b4540b61000c4a1081c00d81000c5c1904229149504015002402040c0341100651081028200c1a04002003ca54400c0168028018010080e004880e400c28600499081d11001c448180c1c0700c1e02c5e424100e1000f8100706400070b4000564520204c00e00c11002d607039505044407651241803555820040c59100d000c0362405a42000c0280070a024002645407180c0689102401c030400c092241c602e810741200003000c0043c04620310001a0380200c2d0203014165002c0e01020100386001d240c60802401440495016020001c05201 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 953568516 1250 953567266 953567273
    0xf03050706140a020408150106020703241a040510030309052707030b1005070b0402150c0615011d0307092c100b1c060b010c1b0311150f07 61
    0xc900611200000200da0b180040300d0f0700007540b03d03000c0d8424038801d6031503001904002040c1281a0340065000d019041c0c510765031400300318507020f02820780480d00b00d040d0300e030040b007486454143c140c45d00c0203001c4286090103010485a016011900d0485008010b00109400c41541c030100d410030340d40410280d0580441c9040f4070341003111180f14144540510580e5585900140c2c0d10610440f010780c071902014400795803a100d0400c0042030083d4000001d0017600e4101d61241910300c195524901d0840c00c242c21a082440498001d4910340c111191071009503404040c410100014074040c500d955182e0300001c0e5a8011845094051a101d00f9520b101e01c000d814420004200040030f2003480c100403d0316621807040002910700185040001e079414640028000b090700a000c150b405444025220781e000303401c0061041e030521903808202070008103c0c030003a060054400340e00ca02c209086140c000d501d201040a0548141495079100f0311030309956080743d1207051502081d40e0750303004915 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 953569766 1250 953568516 953568521
    0x19050901032004150906020a121101091b0b1c0b011803030201020a2a0308100513020408120a2007090509031c1a04020f0f0703020d0f020a0f03050706 66
    0x100c03400040742c00d2841c050008400b1034050000d5544802e80c40480300304220048580d901a4800c85c401a44824804008290304110404050200f071908100c031080e552040c2d800e41d03843d07960490310038083c0b8030039213040344014031001d02400c041a649460461200c200a206480d0b90308000300455a81e05c0c10711071a0b02440714101c440014480d2410a9035590802a00035001010b035000810030811595034a1084083e484101040095401e04c080e802d949003110041d000400c40b100143c45108042202c0d0b641551207000e030704070f10308056985c6041000d81b604040300d144803420b480409100401d4803d8100d22204040c08208d454246400c01e2698094070344000c0350b000b130501e07520341000e00410140204c020100e09000d801004641c41c00c0a41ca481185d28200c19104c1c80c01006200002d44e1a0a800800305414484e4440c1e0601c43d62030412542d55100080841c0980d00580c003c800e11500020748003041d101d540050f00e4030055503194001300314402c420050070420009a80810010941d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 953571016 1250 953569766 953569781
    0x27020f0f0a0b0703081003080d20030108030d060f0e0105220911030f0c060414010507051033090f0e0a030801080c150f091c0b19021905090103 63
    0x70040c601039542c07003402030b840707a001103419000100714000044c0c0c0d0b070988207a110200d0390312a500718a89a01200070500130104001c4a00c09160802c103000c94217081c04014502038500c500145540b02c0014005400301d5549034010500c26420602c108440b0b01d040405a04591058a44140c80c910110b00c1682045407080f924030300310700c2c1c08200018080c04144405603130109400b119540f01c4034540c2c199581440306034850303010304200300c18440b403021044801d0103000c040c1415404e12659030340e8a410a901611031001c200c0d80c500e20f092003101c12408880c840110000d0011921040c0c41c03d200c4d0300c4440340140d2401790703246e00c000c82404d5800c1c1c1c020306129205c1303000e80f08414040d16008203000003e00c1508100d1240044103001840d00c9070742c1000d88600d1410031841c14021364040500e50f0000344805600c82d880500c12000c050111421005003449112846503614150700491290401c1107019030010340306006441015068840e00d202e449001d0501e0341e102c90550b80124040c01c01c0307 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 953572266 1250 953571016 953571019
    0xb0f0d02070b150409020306060f0406180f0513080d020313020d1a09161214030f09010807050406050d09080d020711100305100b07030504170d020127020f0f 69
    0x1016814800500c1c034007405080507107003d0006103101000c22080e03800072540030358107800401c007295451800c040f10024005001d08081109641ca400880d4200c2c1124403c1d0001e07501d6511840c6406010300c24194801d0542a42140390011503c6280ca6030103113850b0056201d9000002c100c00252802c921080c40f41d00a00301d02e41d04d800707442c1810b070090400c0d00b00c08550702c40c82d010034035801c004215007101000445605800310b140010340b208120090000366500c40c4e09800700413000c032085c40207091502c260512a41d036208103000040004400801210402c01d00348410300c00907070b1020840b1010fa07242500030036070200c2030518201510071111200310403840002c901c002c20040c502403048011046418000581c004401079040d1002102c40c840e0440030759405106070360b1248050401c45002c1d1034400c0c103041d01d88105111204403080841d455070301c0030009242480d4240104201400e10102c16140088242c0030411a0124458000c1c13103050a9601c650b096152605040c0d0a03540 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 953573516 1250 953572266 953572271
    0x50c0421020111030313110a090207121409010c060e0c040c0306031104060e3c1f150e01020c09040c03020114070803060904110a03050303161103040b0f0d 68
    0x40c022180c4a68000d03908228045490607400d024001c0d030110549200341da030000203098241d015034904886510360441182d00c840510307408900380d040d80c409441c80314070941784005000c203000340c082d24505d180402c40504e4001040303407241ca82d03404400080c1c2980c0c02a0041249407a1000140c02c2c0b11202203520342142c500010b41e00401e6140d085a01100e02032011421080e403018140020f03220107028001403000d600010030b51001d00f60400f059403010040c0814012101c7e00004944000d5898a442c10040c0402c284015501c44440c0920759002c1519520281840d0080da106210000744080041c468040a4603101c2e034001e20032004d5049005003035a810b49064906100301c80100e0000b81e000030b00303a00c00e541844140c902103440da15004881581165902c9040001419000744104d0f0b0b120308038900303101142c0341c845c04240510322500256850303241589404203048141500700041041442c04410000c3c008000c8406a400004c1e00540c1d80b11078101110b030368440c0d901008400d51 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 953574766 1250 953573516 953573549
    0x1080d1101090f0c090605031c050723010911012c030a02040f06081c0909090609050312220b060603040318060309051005071b0203010b12010504020310140406050c04 73
    0x844008070700c040d81c0178030500b003081c80c2e1120140b42d40da01841409442191040005071100c50003803014001007441040504015021506200362000c25600800030981d1078110910030010040b0580c0c2000c3c1080c6080c0c134031000060780d041281d03070036552030b50340c20034041d4112503c0d030701c06105418803150080c1c4103110b04c0c0302d1060900b00401c201c3c81580d500e801b410354905005201c40c0d011400c40c9205a444600380f50400c2c0c03854008082d01e11040f80d155944412200010380244054101112012141081c4d441c19184000c07260100140c0341111840c0b42c10f001c0d0019260600054015109541081d103a545500c4c060f02d002d46049210007a010b001840012920341c5030b0004c5951600c00c405a0320750201d039134181c1c81503175800e03900280030998a03106921101c41e407000010003940010008100d0945c04c0c404110b655592918104090f5103540401055003000c00c899003020032403503810004140c428a41e00300403030340600000c2000e9200c9000c20103a103040300c19103010f44200742e0f0959807007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 953576016 1250 953574766 953574773
    0x12070515070b010f030b010b030604090c090209010807230d0b0441160314090120042d050901152714040e100501170601080d1101090f 59
    0x160400703141150016030090000c01c2d40d138000740c6100216544a81185656401c0224030251908001d00c52504250781d84c1c0704e400860141d0f5100d40c02002c0e0782c100180c0c1c6201d81c900040414100810040a1292000038850641120641c000701c0c1d002d840e460076142c0d08050221000342c17030007160003035005041100355030440c0c01500303101500359119203202c0842e1020300703a0f000ea400003090760f141c446031101c0c0008007801040403004042400616000a1940001c1400c42840c0c0c001c0d905200c3e5690749401d492030034411008070f44007400071642c00314101494116101d035101001101e810038001e04420812107400842a01005041c00818030a800c0d0307103982e050308901c152211030400150341c028109410403000c2c000140d01ca013800c03e0030040181054001804103820310031054125a4420441403580b0050203450701101d100d610220b00c55140840c82000d1100b03291035020541c00030001080700b0140000c1c840795500035030502c46030302c60183d4400c6004041c070040151030080c1c0280c582701003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 953577266 1250 953576016 953576059
    0x15070525080d0f091502030c0a030e040e010605030a081c0908181002060c090102120301090905011b081f210201200606090c0c1b0102010c0c030806120705 68
    0xaa41c1003500b100c9107400c50b40e1084894405a0b4200c2d000f1400046062013459048407200303805090500480385070041540b08a841c21805410a82c0020541b400720b007101e103018044c41010502c0f6000070b02c0030500b004006078880000c83d01c000c0403210009100103514441c5074411192203aa454204140c4000c0d0500b0b0400c2d034802c0111074413000e000510544546810740700c0100c00d2496070300405180d0b54410701d400c4180d00504d0b46505510450341210002c0e103501c40103501802a03448007060140013403419070300751103078083d11901c6c500b580e120841104e80d02030101c3c0d5212035a840c2000301080b65007214195030f54175400103440310519004006c100e140300500c09100b10f200f070360f03003a080300c0320710402c1c200c60340c08a54a0307040c42d0801030100e01c1900d81046d03102e0b04a400450b6461070080035403070302440c02c603021018030300038021042d501c1041e68082c0724070310031030f11103007002c1e20480b03c1a42c3c014030001c0000c00c0030f40f144420411211490364200020310141c2805072204513004906040e1605 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 953578516 1250 953577266 953577269
    0x10305010b04060b0d0c030f0e0c130c021207080706090812090d0509010c0203030c0d0c0c080c060d0c0c0b07111b09040f21050c0c0a0515070525 64
    0x10150708040400303a0078101442040c040703440c110f1240d81000403454a40000e060910080c13420151507242c5105210b07450310880e041c052400c0b00920103030308e26009100c8691001e6a170503038180d191000703020509802040e4a041d4942054045a481425160013411401000e03800342100380341209030010840320000900c0c0c1c1c07850107000b11000760340741c03d07a080d40c60f04885904400520280400146540035880900b9081d02c003c0682e4281038035915440d20300207201c103115001a40016005060050795640030000c3c103420030190500347e40010118442e841115840900d0581e6103203000b180d1807188001c1c140303451380804024014204108002e250040441241c40103024011240c490344036010b0100c454003401401c948000d40da143c45516003400c01b11000c0e16072041c03034800c000b14021031080d04c030068001c1e43ca40507200c001c142c0c40503140c0111404941e025484006040c0401d9581861021100003030b003903015038a02c86413402e9810a01908103503035031071071000c60307006082100d2240c030340 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 953579766 1250 953578516 953578523
    0xf021005181006030309050613090e07180c09030b06040f0c020309120a050a020d2d060f151a0c06090f060f040807110a21020103113103050d05030103 66
    0x402d03100d106095841111014031000300455114581085503040c05c8014180003e0300c404041c82241d500c085107400c0c0c4000160718902600400d1052081401000b0595418210040100540c54a0b40006840100e041c00054003101c1c804002841a0b0741d16000740f01c2c00c00c174200d4184010710120001a690342c225218091048100040c030070034400002903c3c004181e044402800c40812617000e1000b04d8280110644003605122885440000c44211003000c01c841c01408070300070040c504040d002c0f202c00780c910510007030501c04450810344d104100d83d01030b2900c014116a2003d07880c1c490300d841d0300c1052910007450080c036040001c509004601c0700500c40585082e1402c0e5511035107980390745181104c1c02402880c084c403d0030082103e25545201420018051440e1151103420646007034a0180002c52050040b5155100310759060085050101140450500700b21203480306003c1a8a8486040405803000c00b044040ca402c07003061900564012099451000c03e107080100b00740c1c02404240c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 953581016 1250 953579766 953579773
    0x10207050102010e03040e130203071805011208071101110a0308010509151e1302120a0e0706170a091e1b05061b0a021e0103050a110a0f02100518 64
    0xe1154010702641080b000464099072601e424454001c41003500607110140c1040d1260b01600140c504100319030180c610007a1201161454550800a07034005030490403a41040b40c80040001d41010281d80134181e10690a041d130610150040f5007150702810300c00d801d41308450064041c140c008800c036040e10720680d00d200035540c070042204820002031207003c0d000744154020301c80400c0d032404400300e000001400310340901d034900e4620050781c002001d070001007174181080c842840d0305403194100d1121800b0160410519102015021a0b42401c03541c440061060000e10b5440e0b842c1d1208110562080e045100b0f4540b0300c407104024604108102c0341c000e10200466110196403000c6011240c008044c02d00d4607603100c0c2c0014061005d00b0381115140f05c0c1000030001aa541e00c0350400e490914088881c000d1485400102928000381c50340750034500c1e003206070f0003540040b000c4403032109036824180c81e51924000224642034102e1000c03030002d8640340030f0007413000d903000380081500103001c2107 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 953582266 1250 953581016 953581019
    0xe06130317070e060a0c0c1701150305030405060c07030b0708370c23250b010302040b0105040b0a050a0828050601050904110903011d061504020c010c0c02010207 71
    0x5520040c1c80036100e000100720304141141191401d54000e1014a0041c03814020740c50300c0747d640c0c0007002c0d1550029201034080040c00c000008091146802200c10b62444141440c5540c48075031f143e220300d0150078040da10000341c28140f82002c0010707a00940e800403800034145041c1c2d01c02030000a050b04c42042d580c620000b0108041101c0d01d51280341c01d410815204d004020301c0050380180010f4140b0810b011900b040703c6160b000401d00c20180c501001c2105590703600c9180b030070305500c1071a84a44144c10b98850000042040c0302c4c01e03541501d40c1550f0000309084454010789a6000e180c4c041481140005294408131360701c00c4c0584034180003501c034134200381c0f07034050a40d10101140303030441c8600d1101c0802813995001900115002072041c10268034183d200c402003416a6940c0201c141d0400c0c0004800403141800d100350b0400c43c210344816079007941103000840d1600c4015218034403c0084ca50022480c0c0c0e0340c1c0d411180d144040784006c01034075200713800240196045000c140c0c09070080900 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 953583516 1250 953582266 953582297
    0x3060a0803070501021242040c0e1011070302060c030f030a0b040605150711360601020606031209040b1215060103110a1b0f08031008010c210e061303 66
    0x1481c0e03100110b6882e074241c03a000020317103540b0840c0b81c40d01600340c40c502c1300e092047d20345c903203104603000000e5540e100d5410750b02c18814480b0189110b40510100701000d00d40c0d040da41c0c008a4110152070b070444515603035651000c03000307107940200c9044000100c03002003417150101881c1d2003801c5848040c0c42c02d101084da904100b20b00358090080400e0380c0c0204024400000b03105080100c0c6864005001d80c00b102d15181c101c42c0c2061001c0100a2580104011640300da451802c030741754414801d1008000074038060780883c0d11035004910f031140901010a0860391580c541d00251a43e40001d00b0300c001d81002650100d544071343c140b0200f40140c0308200490b4041d4840d004001c03060307084818041c80c081ca11720049460200700c4004412814a00c0e42c480e0000b00c400e9240611103000b024030903103034100f066240c11905001d40c0300742220fa240031013007026150044011740d5610041c081d15103004545010078005400e1171207010925000d00b00400032900740c1d180c45081410300070f036a46a0039181460 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 953584766 1250 953583516 953583541
    0x20339060315040e010e030406020307051e0d050a03112107030b011b0201030612081b0708371b0b07020a09020f0705010606020703020108090d0f0503060a08030705010212 75
    0x846102d0038507100800c110303940c101504030b1404400c02a00004918400440d0b10b804d58015070060001a0000200344090002c00c0080c030060700761820940311700c487c0713070040c1c40d42d6400c440120405120f40404c0410085009502552014922461840d5a864441d40880a81d40c25814104c40c603024074011a0741e031032092017035495000041e110b51145030207404045503460010718080f410151201d80c0411503940c8044206c5c0340300d204480558981207030300da0f5484865040b80048806511071031040007001d00009a4106504030804108403145c844400c156040300f80721101041e00c1d0244a100b8204003252042c540b01035011000070b149503859060720022403003905800723035000160003c28003c44e039072640108410020790050794503100a5940e00350a5811550260001d6000f00c0020130555030040e081c90342c49180100584003040071600068098549031301c9100802002000056540e1103a01244e00a003030410101d0351111a1450180e02030741c00422644542080301d00464a90504407 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 953586016 1250 953584766 953584771
    0xc03090d11070807030b04050c030d02060a020a1b0c090f0b010909020f210a0b04020a2c0301240f03050703030f090f0e07020d02280203390603 63
    0x66014120800240c001103582800140300380d100340c0511000010140010000740c4011481403451000500d0b042c282141810b25002c8503038020342042c0c03402000d155022919542c440003005005846015802d0200c4074940501210901e40d050851048107100c0274018520881d03c0c5240d06002012041c41c0c480285d41d03143c90305602040122106021880c03164006e8400c803001c008040e42460280580042c0601d1000000c54103e0406018005040a14050384510440541d0b09600c2c1400a00300108510440c13034500809105015201c204402c40c03000045290b8070040003404400307203c40c580140034a980c00c6000700d00500110018004181c00c0503a03088030381120103450828510384040d140309e22004606020845140710229520045400d200d0141003070000100c894540301c1000b9150800400900c020340d840096481c84050344c1509817034100c80b00ac08059110076880c03001c649000d0811001c2c002040040030001e0903202032145500a0310208284100c071090a0300c140491440103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 953587266 1250 953586016 953586031
    0x902130b21010b0607080406080108071d07200309031c0203122508090d141b0a0b010608040b011a0d020a0c060509060105190f090c1211120c03 63
    0x1070441100c408484035440c40d824040c01000403402100010004107154410002202c0e10540450180043d50b0b111740424090081000100702c414240380300d0f01c0d5914031441c20061900c0c000400100f002d4071a140a40b18030011900c0e003109100071000715501c980040c4041c500034032074600d032840151103504110300000e0b42500513500e03280001d0005502480e009140741a003041c4a00c80d01c141e104424820002247d00303a44030210380c10322042c1c4a007044180e480e24000c2100c0d40c4a6680007915001c21101c3c0e01e4080360641260321200c8090a09000d0860b0000d0f0451082c8000010707029088101b03148650310603440f100090b030322114100c0314512501183e00c00442c042c070415445882c180e009101181407424980702c0841d2541e95039060702c00c110780c40b617030a8120000402490801040c00d2150707002d0085000c030780c182490407100d00b0f200c07148508860140c6641500d94814003d6144207034003162950300380b1104188404002c03080d80407a540d1004001c0708000104060045029203004216 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 953588516 1250 953587266 953587279
    0xf150c090f130b0a0f210f020904020a0b07240207050d081504060312030e12041e030b1501080c0f07060b01110a03050c0d09080d0e04020408030c010b0a050f21031b010902130b 77
    0x3119022704c40003c0700100708903040000b044000c82e295441070041d100c298462140d4071114511130314800240102500008441401840082c0004001080d0702c0500000c40ca0643c072240da50211040e200c505043e0440d405c1443d110022040c0492143d00c0c00c13141500740c50500c100c03405110101d59030201804002050a000d200c107108041441181c1c0c550b0203030310307103845058603107940b1403980508007910442000340d640b40b40480c555800021145c4e0000c4250541800c180e40900b010b4510320031220700030b101a65948080344168000c81d83c07982022030080c00c43e640000c440c9001b420550007109002d907103215600190143c00d00c101080c509507030001d006445941d40081082c0e801910394000e055105409220104400700204040c005c00d40301100042000f038410001c0c080f18942942004e40141005141c2d40309035103508130f841c0606408407020140c0f500740022080d06500949440b4007007000c1d0340b40d4060b02a04150089500760303008039503140e0000b1030a8840390454081c0b83c03c490b005030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 953589766 1250 953588516 953588543
    0x111504060c080a0c02060a020f120405010c030810090905060910090f06020306010c02060a0921050c01080a060801050103111e1003090201020307050f150c090f130b0a0f21 75
    0x35000005020f4220980c100242c1c903442d56400100706400c2002154010b13400705001802e6030200300705d65402000240f118074a890300b0140001c024102401c400340a005840c1c0108003410170640c102c03001040300c0f0f2810020910140340954403407400340d414982d28451265100408040c07032052110703076540902c64041c1402c2554038807001e50001011a418000b01000c481c0158031100e0041004d1061035907000304490800b803400c03607050440d038601c40d1014000340c00c10740000c1c80020206208202405c00f102a96225094035000c0d20a60704200042e5003003d0000041001c0040c5514245204541c883d65140c100f0200003081d00c501d0103000c8e80321428668481605000e544034260070390061040d6842c0400039110140b50003a40040d071640c60384489080b041d04c4c0c0c4846c05071030304030003203001b100c0c980105080018540c59580d480340d03100d1118070340c1034407451038603500501c40c0c02c2c0701030401815035035990144000300c44e103442023000b0301c011a14582d12400c0040006440c1c2c585c8a411a00b114 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 953591016 1250 953589766 953589773
    0xc0c01080406020d0509010e070801110915130e07110a0c0519030f0803090115030c1a0715091e05060a0e0703170c07140d02121009111504060c 63
    0x5000500700b03440080e4204840e2400103e00d0007002d02c02d0710502c00100e00d105406094070f00e0058141e0140c610399140c98a0391480f20010421074031448021513030b4074500323184450034080600c12070b451105d0320301c2e0f075250000b603240c0f05802441c441c400036103079404200c00c0454030365121803040c00000c00d40040750400f40884e1070a1050400c807868130502e4001519265070b900605205425001d542e008804000c1154444090003a1b100107140d042540e20710500e0b60360b41c1014260180540740803482c0700d00480308102445000d0710041d5400c1082e41c0c82651802000d0001402070440c1074030083c444480e1030303010705503402d01d941106034000000c2c01a41e513481ca144006115480164040b801040c6c4000701051205000c83c02e207102401c041039446620810705460011550322001800c03090982c1c8100c0c03942c1e0f01000420041d0140c80310120310104155950602e010000c4034025503240506001c01e0205006191140c26010b9528481c103c008003110107241c002d80c071a07000003800c03100704200003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 953592266 1250 953591016 953591027
    0x4030201080a0e030c1608060a0603080315130504030e0a0506030c04060c02130203040305042904030f020a0302090106022d0d1d100c060b10050f07140f210c0c01 71
    0x20a81c00c18156428034600702d45d064140382070010070061901c14241c0074000400d040c002a41c22103645101004082e1a5603500b0301540001083e003044c1e140b070050051701c140c540d02d083c06113040005a04100720700d080d04d0301400320fa400011640c001c5821000208981c20000300300c03030040e05298400c1d81428035040e8100c07501410720000b00e030072010340703000101911114005140514483e40300e0356191414044440c001101c0e694038404c1034061090042507440c005800c07601174903004018602c0321400b900104842c181107038002504024050000102641d01054035018081751800e0030038402900e0810b103204c0001e24564101c160070400306201c656001e89030110a18407040c824501294000c00000c407400c0b64020390a0104406086c100300b0800385110b44028003030122682807052006040c02130141c051004100a41180001c8410620469140c01c82444c0000821154543c00d5004250345030522240001240c2d18080d202e00c0000f001c01041c0c2e00e4010903000240500c1802c0001140c2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 953593516 1250 953592266 953592281
    0x1e0516030b09220503030f01081b06090904031115160905150a020f1b0111190b1e01030f03020705030d1209061407090f060c0b06040b0a0503160306060b04030201080a 73
    0xf032a0309905000400900c0c188041d41c0f2514070042e80c0d01040d8580700005060092401038040314a0700c41600c910150356080640d00c641d02d041d0350f800e240790f480b03280554050b5035070341d02040c6601c03a5914440c07040c00c07000c610622036501c004450014001218003030b6090203041c003416500ca4031303075030701c5041c0c1003000f0018040c807003154411a0301003490700c0030071810651180c001060884a900c030300081c40d41c000001190340c00008008102082221080b0340c2e00d504001402000d8030108000f00c1c465442e841011200c40c00150480e0529580d68070b058180c83e607800004801602500d580081c00f07107400b04401e00040c4803612031136651542060440003e00e240c0c002203d582d90f071040303c00c0342d00f5048610981f084841e0349450f0083d90401c000805000f003281e100800700102d1404a00002d400e0302d044c1600703c00c05030350114000c50887c002039008010b582009416105482c01c41900c11003445401c000c81c1d00560040207401d8440c00351a0b0b66100d9408064003044103880866144180380e4083c56 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 953594766 1250 953593516 953593561
    0x21204110d1e0501110703020115050105071208040201050c030418050114061b031908070201200d1107060c12050705040e040f0f080a021f020405011e031e0516030b09 73
    0x19030b031500c078501a45c03203812102081e40142e5684400c0241100444042030107003200742059800c240440c4d44480c90040e1140480003040a4080824210790140b026140d01c6000351041d2900c03141c0715401142e40201c441a0542030700d0900d00001001e1031400010788400501911542c68900c0611032886400b0000d8080c4c2070038441040480c5100380780d411a4440820305644840711410003000c000d003540c4800e072142606d81c03802400075000c0800c0c18200c9441aa4802c408200c0b0812040490600d000c1c0c001c0241c951400c3c29214282030f540103284a0540c0d02555080180f070302c82680031540c41c0114011000c0c1e406240020030081100c84040e155401d11406d841c501d020790568610705c2a4000c0040000982d1000507001072002e84009040c0411042d5001141000c1c9450002801e244201410404a02c154142002851b00c00d4101c00080c442c038443c4030094000c0b064a140043c0f0303040724190a00140f080d010340c0000d02c07a0084240259004100308401d44075140d414000410f0f07a1030b1071 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 953596016 1250 953594766 953594771
    0x90b0114030408070606090207021314161725020a0305040e0a290a06080621030c1b0907020d080a0e0c1905150f030a0216020301021204110d1e0501 65
    0x75400703006d103101821804801588648a0384140510072800c80200600c00d402e0640d0a20310031504603030141d1203043c1514403c000c100800066031100f0b200080841c0b404503403010443d040c500c030514550318074403442c000d0301035080f114412611190601001800500d04010400070607403580c2c41550044002c2d41c0c0043c80c1c08140915801c20b00e283c206492101e00c12141c0c0c295145414a156401400c0c54102a072a91405800103089c41e1135004828072110070000440107000420030540d0340b03007024082194010f0f0705041480400da0300300c56840c3e00ca00e16050024044038808110484283d255407a8a00d05494800c501400761840d107003580b82901c1a0602a001c40d41c6015001c0c3c0a001e24103800d5060600f00310502030004003c40e8032a00c4000304000c40c91921030700c40c0c110703640b00424000040e10307121103040c4c0b080c81010340e0201030341c598004144121407130742c1081c0c1d050007140f00d40010031015901d101400490308580d00c000d8a081581030441c5040442221141c407544d1154000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 953597122 1106 953596016 953596027
    0x121101060503190f020a0e100f26030c15090709020a3903020114090f1005060d02040203040807031205040804120c03061b0306090b0114030408 63
    0x3c1c003940c10300f09004014486a1100114403507801072400c00030355a14180341c2100507041c1c400d1406803041d0307800041e0040f01c41c141201107079090701c00c2c048001000c41c6141154107080345ca0018a02080001b041801d406000042003200441c0d4124107c1c1001b6415515003007007900001680d81c41007003a540000d80181c00c2000b034100e14490032000080c5a25031218400d401202003804241000f050410540c064200c011415120401e4507490340d0740b01080f41e81c1e4800096210700c1500708000c2c0c0140711b100f0340c000940c042c03c00b0b00750303002d00d1590782e012404030380c0211820303941f0f5040840c0ba40101940100503c81000800c0700a1110b802c064031509040e210740d00c608140c0308205005181004148a0500011074010300104a441c1d04074803a0002a0080080b46000a03e04000410000d4841c411074544040694640c1400401c109a0343c01c1c075030010708280d0b0300150a011 = true := by decide +kernel

theorem cover : BRFrame.Cov 953417266 953597122 := by
  have h0 := BRFrame.cov_init 953417266
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953417266 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 953417266 ≤ n) (h2 : n < 953597122) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
