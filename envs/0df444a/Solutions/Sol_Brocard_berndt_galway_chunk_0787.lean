-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0787
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:47:25.002011+00:00
-- url     : https://prove2.me/submissions/130cba44-57f7-4e7d-a986-b18b541bbc5a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 141366906 ≤ n < 141546762 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 141368156 1250 141366906 141366923
    0x6030f121c09060e0d0f0306030807020906040b04150503070b0403050706080c07020d0f03030e0109120f12090f0b070503011a090f0301110c0c0d150b030a080a0302031005030a 77
    0x10940185240800d4018008071816511041c90b030015040d841116101c000c1c001c002d060024544c0001003001c001c0e18071041c101820f0510420000700611b0544006a41c1151189210369444020800400130301c00840e0f0700134100700e407a1104400355015003040c0e0340305130265881c40b500d0b0804240e051240c1e100043c420390150070100403043c40f0340340c04e941141007295400e1506160344c0005101040346c0c003040d68281d42d900001b00425406124070321405802200070b20211a40d51684506034100692010a000c0c403a0f00e10700700c0380e100e20300c0800d030f0385008002005000e0290030030b4002c00c00051421075805003020042680d07507004100340c03412100b5040402d0f80d081200c99144070607410110440d5001a020180c03055281d0b02030046001c10310105d80070584804030807074074074544a0003034a00b501032001c607414900480e0081024400481c80c02801051042c21003010074030f09400c0c0da00c0030f00903020101f104841554076030000c60060001c001c5103090300d900d038420591a0004140b00800c1001e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 141369406 1250 141368156 141368167
    0x60405010c0201091203030501090b0d0309030803070c06050903180604080613080f18031603230703170a0905010e090f1801061403010f02070b0a02070804050409050606030f12 77
    0x62003508401c41051040c0740c55004199202d900003125120303200100c010075201c0d4018807070320480d8820b44d200540203d50804100301e290700d0107410a20b0502010304035200000c000384917540203004180c0401c0e8000010041c030301d480c0c2011616900100d40103001d80300240701900341c618100c0c041d40d05440c0c01038040e06541e119519100c0400c10100411152440144180790419000c00701600c074404800e100f0208100c0020b0405051a141e0b82001514074945102813001c40e450020130786000c584c01030086480803c0a82c410300e4240b0340ea000410101c0e038030f04600b40e070707611110151032107804a803217041200381c990005403107040d918484141c011031344d200028042040b402065401480e084011400e00040b0250142502c440fa08201e400340c2c0c00c4440215181402d104072140c3d440402e9046040c52031a941c4c061505d2000b41640e0070710f82d008520241445009811a8000e044c0100100001c500c83d00c0c0482d1511000c035003851288c01408400580d548011030040c1c0d00d000e00c0007400e841c02 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 141370656 1250 141369406 141369409
    0x50a0506160201120203090f101b0e0609040504051501050604150c0311060907050a080c0d03180801140603010c02010c050f0a2304230a0b0703030b0a090509010e0606060405 76
    0x1502045400da0410503440811002c4d42900e03c002c601510104002d003140d25403914126242103481100b0038442881c001c2d14003141c42c14030791549003d000e10701c0d03c100001d81c4a0700042550040c52011a0b00c00d10340418001045800035011031451000b20300014540c5c0ea81d4208500c41c0143c2c810070450588803940c030b050680c4240b40c1004054485d0819414030203c810103030f8035001003200e0004555002c2401441586003100c4603030b0080150500a0080d604800e0118200d0640031000a040c00b048240e4101500400d04421000d1f1450f00c008001003e080c40b0f40c80c51110040d184c15019500c0d19071007510301481801010030300406c2d5140c00f441c00a00c10045007072640261036540130450302e1814401c1c11661640b8600d034103014840c1490302e803414494130640356010401c419101d40080006101345454824811003101d5814900645500d02030a0036409800c1c044003842d809549417402140d003a80c11740c0024010f0440c1802040b403404400c0310030380c0d2503e0684082d980410240300030443c030f = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 141371906 1250 141370656 141370687
    0x180908070f060f0e07080f030403111207080d020c010e060304030804150608060112030219120305180d0906120207150b06090d060204030b0c0403020603041202030c0d1701050a0506 79
    0x840c0b14050005150343d1040e0350804940d00b11400d400644c20100c010410b0620810840060707040c584061490b00d85155280c030f900c00c00340c068142c01404810300701d240303260042c84004001d008850945030003880c4c2c5030b0002d4035407100b8204d80380800c0300029501c14600f81507054038803d6900d074035400010344860300c42003660081290103114990300c07402c0c0401c07626028030185000703141e04100d6002035006c0340b070007a0420149000b0403103140140c103010008900c00342580410301e0700f03e00740040c45841d0060310749000d0140340511142c40c400d90701c4240810360720845640480321550b032020380c0e400c060300c5031509078481c07400c0160840500c00c0c7d0010b640c100c240e002d45908070000300650b01c0d00b011140800c050040000040ea400c41d8003144c00c000348801e02c0d41c115070000c00340b61a1442d04d41142d000502e28080078201034010313114111780c050064000c00403100404070100454251000c8020020300c541103144015504188a600008503410402a010203541004110a04008100002216 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 141373156 1250 141371906 141371933
    0xb03070609063e0604021305040201081b07020a14030d0801180b121f05060901061b020a181a040603050a081c020304080301031a06030607030902011103030c030118090807 75
    0x181442c0710f501164036152a19205012454640c0901494a0203004120466000409001c0c0d42800c0004000c010307a4444083c0798440b04021082d021189401e1454505000310303280250000c00046000c1076500c42c1c01540c06001c2000c804603994243d80c507004444c0e1403001e1082c01000d00c245003510354001200e170805848400c002d0900c0c880d00c3d0303550403044c0c07402070300785507803061b1511000305d03126440c06034000c480d0700c800c0541d480c403215490158014600180103131003001c149182805801150ba6120141d80100009020703060905858a5842e000f041d14258046d0000c044452040300c038240750144404503034004000c2d09415085444a2079141d006519280c0d0303180360309204d42d030f01ca445403026500803400b40c0398464582d0704602d02800b800012151407000d9032450000c120341030341d00155080e800212807070045000d07099440140c840900c02201c0c86214003011003080505c8044d000614105c070003d220b25542e2081d00d1071000101c42caa840080d000bc0000c201704001719020114044 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 141374406 1250 141373156 141373217
    0x10b1b0a261905030702150c2703010e030309010e0f0703230307060902010e0f0a1505040b0d0510270203130203010c0305040501060618090902030c130b0307060906 72
    0x10b00c0c21440302405400710b88030602d2080412000720500070010303030400491401c140d00c2a05806035080c1802c40d0100c1d40100202a442c4909407002c6404c150601d64400d1070380317035010f4005e11002000b80e018071b85a801c00c4818600c5907291035681e1941e480005421b08080c101d1201414200781180c0b43c01190300c2e100d504410340c2e040ca003020042240390401c01414424026800051603c0c0d092000410f0055820f1041d44141c0d170144a6129607900d0058120450318405170f00081401c003a24169802e010b03075804a00d02400101c0d1040a0040e96001303144141c8401c8400d203003087e1030700c004a039440c03030b01c0ca0030400c0e84070007204011849200b42d00440e0000b405071280d844202e07c03a400039083d90b6a07845041c00198661051008014090042501800c0d20b41482c0195207031503015004000510f01c1544d100684415408066480500811032000d078040e102c90318004658800390090805952804d010b0300c103040c000a42240b088942406035003c0f9a11a04680003260003003028140b00c070240c0c2e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 141375656 1250 141374406 141374483
    0x9151a0f030a0c0b030901050c032e050a1d010b12130501090212010c0207050604121707080304080406140a050405010c03110607021f1103071206030506010b1b0a 71
    0x28800f090404002030020220703119907903070368a0910b624509540000c0c140c112541802c0c8144020030604000c1107075443c00d40c0ea01b0814480340600c40301301c8680315500544d080b01c011000450001c400c1104042084500d524480715a40e07191040501c078880e0080f101c482d0046200850f10b2400d910200748a42c5000e03600203d0801051b4001071401510241d0303000840e0341d11403c2d120b000707406110900051900312111410546401c00c05401c006c000040140070b14095075003805141c40f0070341926041b542007143c2540f02c1c80c2034a085001360740321b40501404207000070400d003008040c840844070004899518a81410320380390040d030f43d2209420303040707042c040301c52011201818100052071003107245900500101080c42c041c0e1004401d410750079a4418205084000201e03070b44811260050740c185425255001d20480c94170040000b41c100801d14014900006940349444004d804008034441c0d0316021080c010380160358502c50600020300d2102215160007020310403070560f41c0c03a03194070b9260 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 141376906 1250 141375656 141375673
    0x142a04050f1302041a0a020f0c01020d1101020c03030109140a0c090e091c020105070908060c03010b2208070e071803020420030a09050708030a12020a090308070609151a0f03 76
    0x1485c129070500d440609402c010a1150503140d0402c039100315a082100a0469a107030100002d4032812060442c0f03081c0140c8100200c10b844003581140e69100c01c03c01540d4803542c403480a58050440b9400b1100841d0901001c602403084034851580c0c580040c0d1203501c18a0300d44011402c0d0310703100400825050190b88125210000c0290040b011810158000200e9141030140030702004e60769001000799511070000c04c000d00000301c0403641503504080b1159210001e40c0c0380c070100a00c4c43c2a1400540c030901c1e000003040840028440c080d5441c050090040d03907103466040f02c0304208942c41802a0002940820160801d40d0003441c2e00c40d419446010f09155070b4015072240e170300aa4002901e80e5458072500203004041c0107100140c01014040c5150210301c1c0070080ca291074036650651034a40c0040c005011b0ba0040320000000c542c8280c145841d18040c2c02e12074000c0c0460241510f0301b100010740055884c096104125940025500c0105180b40c00c600344a000c080c80b0300ca694042c0b14a048 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 141378156 1250 141376906 141376919
    0x607021801030b011a090f040e100c020c0103092003030f130305060108030c03030103110a05091f050a050a0603020912060907090b01030203040b0f04020103142a04050f130204 77
    0x1026458240351405801555265203800304000005071700c981e18151070060100e004a200904850b80150100e0350464030005d100c0c00500202000783da000141d1181e00440c6940851035044a012810720381c0030383c0c0e03440b6130150064081e1004c01e180101b1800da0062280701c0d030b0b50301202071540300e0006000c403401d022803035401481c82d90121008000c001400e5004000b0000d08011040c09000004040d50800b03058030a0b0540d0fa02041c00020310b00440000501015110448440010075006140014078208810709540d0359030203184400c908a410500030400b41000d1000104807080a8160016a454240110000e41011021507800341a0400042d1031340c1d0100205409515100c1c040c000c005e1030100400111030700c0c0031001d4103160051040001044409100603880481d041c0074000316a9103100403401098035080c00e814000c400020b0040d8818041c900050700310f101040c522598542c00c5a5802c40d0165215180e801502c0d0a510302460030030488455125244900260030700b40c8940313 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 141379406 1250 141378156 141378169
    0x30e0d0203070203070515040b07150c03020408252306070305091801030206070206070311062403030c0304050409080c01290f030d110c090f011e060507030e060702 72
    0x49054005a2001c82d12030b066140c14403180c40180011500c4081380c0c000c00340000f041e801340340b05e0003095000110300c01c01070006041c4a050f1800346000200814551a40080e000b900640a01002c910039664450421082c0c40c3c02e481061091a0900b4881c9103443c08501080d04540d440312002082c0d480c039100c00c1d8448101600e00d0a00c00e4941644550344801840780d89100c0744036294240003000c00400160315140201e80100340c064a10b40c2d501d5420382802e4511694044001203a4491355003040100c46500352090b100448045c0c003035031034410b04003c0595034001c3c41c6241c900c0344c03c20030041240b0b03d4039500440c00140306105d481e003003003c41c4c81c1d41400c4840700f00a102810340200900203d0006801c02d0780c080500489151042c4810400860ba850341c84490b11400d010324500c80706c101100c10003401480c07140c018805201c0345400d0612045101080c458110445140d40c94001160100584102a603071295602c50900806480c202c0b402100e0b6003903180c11410130803072030015860f0304 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 141380656 1250 141379406 141379423
    0x20910180f051303050403030302090a050607111f02100b012105060109050607081606020d0603061410031a0709030b0906060f15040603020309010f0513030207050307050d0303020a030e 81
    0x10005a041400c1c0c1020302036682c0203181d0041c0610300004600020b401c4401d580c00d40344c152500507103507421800411229034681d0440795005102090440c100714400442807000303c0280c07080c01f5000e000d4800b0011081403c21080090780111000d940f00210342e40c00301c80c101d901450180804103002c6050340000001441d00c000c603607290802c110b803558100c0d0300d080c010300307054811034640f038071540f80c1b052355003c6c0c03800181640c2640540312081c45050340550342c0d40d0804003800c22503d82d81e490454001d2801d144020718a070075583c0099149856155240100e0b07401030120440c0003c0c4051000e00390000400f02c20500405100100208038450141d0f4495900c61004255500b010750400c20000214804e45218200c0c5ca90014400300c954002d80301120308a05000d03031070f500e9540c980341c050070700200d1301600c15241000b00070511071034113511014079000380c090ba03800b5602c820a00d43ca810050088940111070083c3c1e180009119500420100c08035150008058085443d12410700184 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 141381906 1250 141380656 141380699
    0x901020403021f020f060f0a0c030603080c01020a090b040e0601050703170a062d050f030c090c040e1f1206021e0a030c020601050307170703050703031e0206090a020910 74
    0x40c160f0303070210781d034040202c041351400040c01400d480c40c0805890307118050043c01100000d07110000d0326030303460003500490059030380504400c0c0c58078132905c072240c002d400241003000042c20411000440107044000c98054030400180800303245d0741d00c001900d4690028400314200a41041e4908200f10812400c5000318030000011a4880c0b410b40000d084403e0310209595010140c51207400d010441c5100108030740b0142d881030300e08402840042d0034011503082c059002605481000b000c940c030600140184c4001300c04e40f4445071a00c01d138090a4a000107009a07030301c518020300b0320484440309441c401103846101c0252516603d400c123001c01007281c0140022103d00412910100382d054000d181079044103100030080d96140000095681d0101d100341459150329020b00006a5002c0c042c40010710341110803900f180e03031382e0f19000340a94403034a40d2007042200c44a180700318500c003084581c0140c07285001050320140325020026450409000ba1002460b42400042e030400c506149076611a02c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 141383156 1250 141381906 141381949
    0x20c0706030b06090d06200301030c15090b0f031003050d081501031404140703051c0906030b181918060c0207060219030e090114041103100b03090102040302 69
    0x30305103018040c1c03040c520b41644280030600400c40d240c0c50f40402c9040071900800d0220300c1b510304520070f036010040b0442089040758000008014881c0f00d0490f94201e0f1002018140364180c0144101d0b000d001c40e02840c2d0407030740108074000b5640c41c21006590450724501401c81c000e6030f40d03681d05281c903c43d400d801010807020b1040200308121036044101c000000c0c01d0521510a0507010718170845001003005040e40010310f14600c00300d07020841c2e400996031040c01ca9004c82c88800030000c078603508000e2040016111000803e00368403a000b80c150007078010382480703e042a1091001402c0d00001c2c40c0845104800d12002102c0300d03e4014501032100321380220007101134504080c4255112034424000f95070260008018050380081c0d1001c4110a821500700040c0c21791500301c404400c05441315038081c840000110f2200700c81806151903241c111020805500910130304203860008403030302c50400608617420040310040500550348040c01800040c6044e880b0341c0022507603072403448202594030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 141384406 1250 141383156 141383159
    0x304050a08010b09010e1303030906111318021e22061205090c0f090c0705060c040503100b060906070303090c030809030f07030b0601110a0f032106031a040510020c07 73
    0x1380f00c0351132409014a889110481c1c80c001c1d004071014411203a0090400d50346180b2042803003070580c0310044581c03015400c2a0742e4008101c0007407082d00075014203d1140c2249100b902c00b030465108641e4200b0307280100350141c40c9514140000d80c0c01c43c1112001401c54800002c0d07900b0111b4034004040e0031951140400d0140380040d82c02180c0c07000741041b03425070101e030704001643da42c4503807026003100494000c1c0d01583c42212003080c038004c20b08020040d1050340140500120380030098010340e10150203c60646940c18075900540d22843c506035040750080140446c42d003402d5000f008900d020703003004203100c2c5d0942e45601100700554819a94a240410804841e190511100306e803028400001e01c0f0842c11034840e1102442e000d010541802504110300140c00c80521400c00c1c40f40d008643c1c0541000d41e400c1c090041201744046e2544590030440c41d29200120f44282410b40e904014200203150b944c9550325070000b400b400c180d07154458040d0411030b03440540024108903450b40302030124079 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 141385656 1250 141384406 141384409
    0x4021012090803090118110910090504050a0210031b0806120316020a05060307020709021308010203130501061a07151107150c0302030f04170405040903050c0c0901080a03110304050a08010b 83
    0x5442c0080c034100f80260000002020036488403030034072070107c121108080b0703844440004106c1152980300840c90341c20700c0204410700c6000315000344102c1c02902d030013038041c16042d8110f0484001c2000252603411139944106524032807211664084800340c940403048903040308032440c42d00444010400c4000340391003070045050032003089c0003d0006030342c42411401c200f0b1000c2d44481840c065803400550108116100803c102035280080003490001c42d960b040a1000b11100d1515140c10707122582840000202802d002003c050002c40541c01e5034105141d40c1d884506220380f0328004640b2907112010303120851903250003400c00610444500c180160b800000f9800c1d00d50388800035060610505c20007140c681a0500c407944103a1002d0003031410403a1410003600e0f8040c9404c85904645400c51800c10590028024640d41d009402210240d02000080020100c0c0034000e40b101a007080d8843c400080c0030301c4042c07561607841000c0c3ca0405ea2500e000c6003052015900c23103402e076910380c2020000b5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 141386906 1250 141385656 141385661
    0x19020c1e0f010f02060a09230c0a0b1c0f02041a19080609070c0c0e13060f1b050703020c060d061e0501050f09010903060603050105040314090306040210120908030901 73
    0x705102800c11111078400d1000207500d43c40028400140103407200c05c05020040c1501100d4450208152550701c1d681a00705416500d09503507070b03128080c0d031122402048103409401900e0021a00c8680b902c091000000c40001801c00c03c410266950780a00c0080b450741c0305003000c0c0e091a61024242901c0d4614032080c1d0350046000e144141c03d00248005200542d114900318951040807030421121403a03552a051420100e10341c13001114865002c10320a4000041c581d117440380d03004401c01c2c82143d9450b20000b0031100c5260f080528420080c10750402d65015001500c3d00038068010340c1e890403410b5010840541c8500750500d01c0f103030b03910404d008103c0700011600c40414002000300034a400c2900103060b40c0304c0d10141c07900000300850450820383c4210005409503a0001c024051583d80749007885c007070541924200c0104001d0201440404103400c15607011000080c000d0206864075024850034511241c154420807200241c4803900c483d05004042d9102c4c803403c4501e68038503042e038501d403c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 141388156 1250 141386906 141386929
    0x311030723030601020703030503070c0c06020606100203120103140a050106140a080a030f030510080106030609060e060f0103060506040e0610060206010510050d020c0319020304080c0a0b19020c1e 86
    0x5070310340034814040302d640e0000304902079035450f0910365a66250f01d1410340d000420540020302415071494045032180d03002c0b880754001c10307003a24141d800d1075011900340c1e12802030300c0c1901c20100c404001000491a401c03a2b007001c041d0488103441020340359486460075240c2a4200c9807a8440c0f91030910b050b0305080e00042c004100c0c03080a050720140b142e074010060324a80007154100b64503180032a0150451183ca60010900f600081000781d42d80d1504802400c60000c3c01c0d1200e603d00450006910008108144600f04048409980d40c0c01c55882c10000c200203082c098000e9940e080e004050502084900d002c1d90320640303000b6410f803408200a01d0a501600b0160042a0f0308114690468003c000e4605140c80d0203409070326071440d521103600d9401081c0c99030300c07071050614404101a4010004109503607043d820b5503044420070050001c400b00501c2008140c003000c11010313822910801d5085200501441928000324618001911400c4440311410301c503c00305028140c02c1c40c04042400c07 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 141389406 1250 141388156 141388217
    0x6040f0215030f0f10120b0406060e010506041811030f0a0501050f030c061602030a121107050a120303060906090c110109030801030b070909050c030f0907050303030601050a03110307 80
    0xe156192041c3c001000e0306010346030401200b054004070b03400744a82030120019041c0d86040c81d031003c0113803c0115403c1d0054406031f6406240c8800412000c0c1e001040d281a10000750a440c6001c0c90844402091410003c6d00c0ca0304a944507025030601603054001c1d030180d41b20b0a007484040c14540c10403400c80d034041c0e20140c401c10b29050ae500d1a41c40114051184880c00c84406440d003c0400d4141001340460b60025418069107880c0010001c41c0290840c0d046a00e60301c44001c11400d4400a503500780c10b010707107644448070b0381c004c00c0051810141034075610f1080c40d000c200d50f0b0399400d0b0081698113581018084507166060643c1c00c550002e1590030a00f05034000b8845450662030240003000b06000180c545a2030748005445076003d02d041000410783c0e40410019071038800017801291300240c2c0c030800d0f51903c030b90100f0740403840010200d040d103030001e024601d16240c820040d20190f10505a2205054941c150765864130700510145100e00c1040c0c9074007111506615891030309507000201d00c2e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 141390656 1250 141389406 141389449
    0xb0a0615031a19213804030c020925030204090b0105041406090d1a011d100e071404080604120804051b0d050102030709060206100806061c0506040f02 66
    0x140c00580100c1c1e0000300c5129042c914007180700301c1d912138468014041e000c0e0085500e0b0303407200002d2218054940811103500d040c1d10b80601c40039070304581c0072010f6401a000920110b103a0700075140440d00140c200406e000c140c150401c000d842405072042840213103000c00e6010900b082606494020160052024070b4524601410709031040540d581101c4010b000c2c5002007201d44264583d4218115101d800900c2582c1f044200855000c007014240a138800d4202c0b003458401c04050b4011515018460890360090001d04000c0e0182030104001c050504008a40c0f030b4115036071445038000c1000d000c400000d001a482c06061603500b00040c40349010811910808010204030b0119500f001004001308004541521030002003100440060181031ba51001050101440d0014501d0048901a800340c3c2e91a541d4819440c04004052103102c0958000b2400160285040d484a2a1104140f60510310300c030000c1d21001d141c564121030403601010b502404905516010098580703688034401d11 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 141391906 1250 141390656 141390679
    0x1080d090f0306090302070b030a0204330c030e180907050f0105040909030207090516080a02180d140a1202061005010c02091b0a02010204170705010801030b0a0615031a 74
    0x901401c16460710000d00443d54039071000c410544240a00710080170f01e000c0c2203859003030803e0b1074002513026104200003c0b104001d1700c000c1b030f035001c0c40036484910701e1401c0080c10304049074260b545414010045003048111a050481a540c4105000c0071419281251805140c65000585010a20b0300124420604946140c03041c0c5c0e4894200e4040d15030551001c034020541e4501a4a0030109801c5595800e0900742042400300505980bc54920101c0d5900300c45034480f0a625412407040c184c85152040c00600703140401d080c0000c0600c102c0d071143c00300200c3c0b40352417188203081804183c0d013200e203c040340280191156040040c981c000c4041e11148960070318090010300000d01e41c040085c0900032010020b0b540c50003e0480780c01d40018086850356603403250030300900079442409540061014148852080320b00007481205881040c0c45040c0b0307907400c42d1070701800950001c00c07c1c07012a840306400704000100000c0302c4c43d00c08071528007044001f17031100783da01840b03110340c4064000c00743c0c00d06 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 141393156 1250 141391906 141391919
    0x50f01020c010f110f070309090911041802011202090f12010b120606181302031c12060302090a050415090606141f110c18041707050a1b03020d0b01080d09 68
    0x705d4403084060042c80d45c4d94552441c090701c4030f0a031540840b91072440c000c2e130343c01803040c8040607525a0108940402c40310706044802182c0d18051032010307000074003032000540541025401850155402081100c04442c0303040042e1007144075000850050f5152a42c4442d00e0a2402480016174840c801901c59445c04030003041c07490182041010040b906400030403901c0010260f00c0396000e40107010b542803640c04140384113400c800a05071200140c845000700108007282d1080b10191ba130b00911a40198541b4510319000d131002800c15200709002d411810104043c42c072070b0202d0300c0c1c85050040390862528100581452601804500602041074200120341d010303d680821005c19090204e0585902032a292030110420045e5030401002e17080c40e8010b07250170a107244294403c51128017003040f803120f2228940a855401811588240d110071300082802c6200c220710804280d40d584000d1f541e400069130741ca10301505503845035407240107118000b418468040c4008243c01c020550381d00e03095 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 141394406 1250 141393156 141393191
    0x70b0702060a03060512070806010501030903020312060609131a06030405150907090c030f050702030408030a05090d0b011d0709060903030e040e0106080303160f050301050609030a050f01020c010f 86
    0x800280301e0700000502020240c026480840509400b40035500683c42200759140d4a840d2405400752601c40e200001400d584a4064500d140358113502039414450910740a86000501402c0294000c0c070a02c0846880d460b00029017080c1d203038103400031070b815280c10903407488543c011a50501039001081040042000040d400b03003042c600040094065039410800760405030281c103d00d081c181419401594103a0542102c600085a10f40400c09515030280682e502e1080780b141201c590414403d0310303203107409480070304a0a140902600c030340e11415500c03030b1800d030002d801c042d200d03200401641e0408a02e0808a0358004403a0600c840c00c86d007030081c0948025042e210003801c00090300c000011035203c1d03410010403200c2120082c42001d440d8040f8646a400c22a0440105800c0c81100301c0001e1040280000001154903124a180d00384001d1110650000c2c940030340501c142c070340240c0003400400694407112000400103032120b607124542c0b0f003980e202c20907100e1400e04040d0186a0700c80c405 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 141395656 1250 141394406 141394417
    0x121509012304151a03060105060909010308220609030b0a151802090307090b0102150c0d0908090307030c091404080904050717130314031303200303010b04090e070b 72
    0x10503554506980d14030303008083d070400d000c01107a400d04264454400b0480c140c000e152441c000c6068590036070302c1d08280100c5000e80000e45620130030080040011584071001803a4040c1501d07000c07018085006000c0e01c601e0305a602460005048050030404d204c81c0ca01401e80100e80b940040c420702a440150004650080c014805050009070300415851816411140e1114028040c3d601c4190703141c3e0840e00601c4c05400b02c2d40503000704110505080401c0078514405c0eaa2810200d0421310340341503402c0102850b090480d60310404110001907a64204080c40042d071082c0402400039080c12852001d582c5290381021250700501c042c000000d40141c20b603541603200707a40000703041c3e4038a1000c643c01e10500740c2c4500314515400c184043c41581c485031500050084c0c5403407075030040e816586c0c81ca9110407a0303022030146414145000192003a00000d07101840741d40d45520f030b141e00c1024503055a000780d0000100010014080290015034020301c6401844074028104541c640304004800d843040b07 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 141396906 1250 141395656 141395711
    0xf010504020313111315090e0303041a04031101051f060e030a0b0c04170304050f0a05010e13020c161502030a0807032304050606040501080d0203040b0708040512150901 74
    0x70074046500d07000e034100c2004034a40d000f03004c850101c990341242c498045c0107240d07c0e241800c0c0c20f10a28003000084a01459103c201049200320300303c00c82140080141c422410001800300402c5100001d0007114001c0045907468440d00140246145807035129a1101e0f00340a50b411070107100341e40114800e40c0e50307504441c0c03119950365038400300c02d00b900c1181c0101808803200000683c0281c800030140007982e8059031460740c21400f1000704541c0029510400380004c07055400300840d410305083c007111081c0030740009403d18910022071420041c3d08a04110b6112402c4000c002641c0c1110350072085020f07900240d1310304118603c000780500c1d00100140241a243c00070750b1003200130f90210340c810850070582c085650809180c01601c4941c1950b040f4412030506002189101000c62200c0032015980c006524003403a11001d0b00e580c0d080721405403006201413200092549602d885102c9449065010f402c101c001d1410360300d150350000d0f061681aa150501580302d034482042e010031602c02 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 141398156 1250 141396906 141396923
    0x109051207060e04110703050d0b040207080f0a030b030d0f1e05040b03090a0f06020a0810060504120203010204030b0f040312060503030a030e1903090f05040b03060609070c0b040302060f010504020313 88
    0x38018081130103810303025454801d9680c0001c254051543c0003000d00009022800288800b454100c02c210580c011290050300c0508208044180104110004e059555490401217614810341e00024108007d107000840400c402109230f65a580c1d20000a0310010580c4021500590701c82d00014014021401212036020000020840b104400c001c00e146290b400341500030320314098503044000e500002c034803101041010002c100000c88503030400c03064680c10b0b0b80c0c041c24140740501e24088212410402c0e60555402c12002c00402c0380029030b584510303400c45450304103092901d00141b01403801a0314410903403400070706000c595008800c542c410035803861301141203c51003482904007450000e9003d802800c00032a181015003000003d0112410207404d500c200781c2e94000d10041d140d405d491181c0c9a0407500024020381750400d86030b42c0106203441e04440203440d90307070341e00e50390700090701c0680260340120100400403854070f403000e02400c0191010b50840c1072503040d00d943c10309000d038020300e01c11 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 141399406 1250 141398156 141398177
    0xf02181012080d0b060706020f0a0e010c030c02011d09040f030216030f0f150c090302040e070609030f0c0e0108011e0b030303060108091f0b03070603050c07080904060b18010905120706 81
    0x345e03540f081d503003219080401150750302001050204541d01955030607010030096150882d040d07001d02400c82085070542c0703460300500100d6004466200070b818104000e969a5400c00c1c01a44172501f040380314500c100902d510400c02800c002e03141020702c0750507580d0f8504001091002844400c0c08100c41d681c00305941a5a82c00c40c5003030b0f4100118030007001281c514000347c0e6100245e0103a0b00c0000c403802030f87c08004091007540c81030b80f40d0000e40a0307030011a0143c803080000441c08840c0030340e002e0103090010010380d03e03035150004060081c0d100c0c50880c5e440c3c88079400010400f84c5980d00102461008002e125011400709860b4040240a1414844072400040803a030b010f00068900328810001746d407903151407a07482d1004000d4801d10303a0213407050b8000807907442d0003846118000c240c845141424690280d6905009511080340d690f041034a03108002031039a00000034103448045054000000050702c00010151000c0354441d610035190791005905560011a0b0034040d00c080d45130008605 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 141400656 1250 141399406 141399409
    0x501051306051302071a0406050f011a12041403031603110909060d02010306080d020a14030f030103080d0609050103061b0c0b13030e060c03070b0108010c050f03040f02181012080d0b 80
    0x1021106d0084207a0000c90200300400c907096000c40d100b040165141001a6201c6030402a0700244156020f03c4140c2003280e8240d030440000c0032a881031003180003008240d0b034240920f0442d042070f1042c40000c140c80021014040c0c250040070030303481c200c0d0106810000200700190030003030f0262090340900e030355100c07250035a4420307088080a00300c1c0c402150002d00030f041c0c00a64401c112441a0740e0406034003000c03104810b021007191500002001440d0443c2d0a5480d80b50352540b103a5038140105503034607000038100d8042d00a207030003113001c1c4000241c15444450031201240080d084c107401c1160b82b400792000208403d1369107801c40d804000c660407840c120726040e104000400d112503030002d00424240e00c01240003000b00308980c0700d2a0f00398050b90742e81e540603007a203c0c9603c801d4041030f0140034004580003954051a801400b404141c1c4483d1050f8000c242040c920f0400c46081e000040c007004405610340c49420014a0205000030741149662240b40c140d002e480c44844444c0d86a502a0945 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 141401906 1250 141400656 141400673
    0x3040303030b1c0c05040b01080103050606010e060d060b030726010b16020303070b070314010f06033602040b01091202060702031c0801030605060109180b190603050105130605130207 80
    0x1a204501c0c04500307010070f00d040030190300105224180c841ca0401c00301c40d213603512583c0a24100d80d403000050003181c44081c01954000c90546180360803d006005181500b4054011040144042984140e0b20306245100512040e01d803001100c0940c441d51184451844414500307044502d154603580d1074812540343e21180e05034101e40a5030512020402c0000e00051003000e13401421140c80030406000042c0052000708402d202c0c0d40701d141c0164200b0040d007030194200b04002605041c2c1c1d038580319000c0e6007084090320401f03400c40c0b110428401b03070350031800e09101c0c40500352004d00704120124a481c800d80880d902112001f40243ea001c16154110349040003400c0710005041400142240d07030280c02040318500f4841070301d0305c07402c0802041155001c0c442000036618070081080e511000850300c44041c00702c034541c194010720300340c0c40c0303088150a11040a000c0c000780d60b000700e0a035240c80c0c10040c240c1c042c803d03100d040510700b030402c00866540e012007803651100e4440c050f881f1485824004039 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 141403156 1250 141401906 141401929
    0x1506060d06031505010504050c030a0902010507120203030f0a0e0a0201200604150606080f04030f020c090109020a11060c0733090201201b0303040306020406080f0c070503040303030b 80
    0x6918107240000c0704000007108001c40c08007101c41c0400c130f1030b0f0b80c80c010002521000d69401860b0401000440c1002613150860707681c5038010f06006142c803080e950b1780c00300718012401d0b6400507000401805030340c2c0105500250460782c640f105101030103861042030740315401800001e050000d50000d01c1c07a041c020720300048190090b402507803000c0c40d140c10810841e040704409500c2c002d203030400100d40c040c06100c8660081e2806140c1c41c0c9243e03125039050f035299005202c20425482040030b400c20725510107041c3c0b4003901840c14050f8440b003107103801030b02240c0c6000e10304c021074004004010310324105038150b0302d1582d040f6848040d40040070100c2c5840c0c01c0201e00031810030021385908100d010058000d802160320030f90b120f4141c580044034560201071503244011281d000800c0da08944a903611035014080d500070141d0385010b41c4d9540380000ca0340254407030f02c0071400c50010004441e010a600c42c0d840031090f0500c0b03141241036622552a84201e00005080c10340d00d03104e92180352102e107640719 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 141404406 1250 141403156 141403177
    0x8071b261e0c18010f060c1e0302010b21060714040b0c0d08070201050402010806130b030105090a05010605060c070e0c07020409050c0a050402040f09091a01030b010315020301030302150606 83
    0x40c20100d801d4220351030720010354102e0301810071801d25041c0c001e404040641200d000c810f9000b115824001c1c1103c200b80310038825200950034a40581c50090061210240c1a100ea0000500710b05180140314504a124900001c0c913000c048109140301004100541e0000c07107032810114003a0300c031400100c68011600105048000404c5c9a2003240300060302203228916a00c424a05581e4404128241c880841d030003030001da0400c01140250800441007801c0e0001a81c01203082c0800030086401c650046070100403581c01623a045003406028031078080601020727240c19103010b943e50411995407070680305060501540c000041d03079800d03855007600c3c901e0703034020001c1c80306810300d050850b6256490702c41e2a1184c900010000341600d024401c0784e04403020032040c2940e083c0313000e111800514480307500790341000901c12511412540e110403e40a1032103248081d0680d411400e00070526140a03108800c00c170b104100500229030005108655000d035200642800e50f207900100b072950040b001c410 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 141405656 1250 141404406 141404443
    0xc0405060423091e100e01200d11090d12021c0203030403020723011215080d080603030a09030b07120f20040e01120807080708071b26 59
    0x4402103800c0b501050b000351007040890f05a0a501e840311000c0c01a120710005681c0d2007140003c10a036015000ba82070b01c802840002940c040c0f9900318200440305070366034444980c1c00680a10000024498081d01c0c4119111603400c2030205004590440d0101101600031844120384454031842000340608408104000e6280c2d01c1c0d2403c1e0280d602d400075141140035000742800421179104810000c0c82480490740020001c107140e0f40195030f0110034000c0e0801c4103445040410001a8401d04d4000500f01074004101103080d81d01c0080403c0c40c05400c5501c0380d04100540c1800c42d44c0416030b50180d035000441503805880b0081c00b518803079046400c505c0c6003402d00c080c5c01d4242203642e0041104441a030030952105210303280c0d19050340700e00d028020103030582800501c9681d00401504850031b205104079803816425880d001030316001700b9000c503540c0f00009030f800c04001c0261490241d00c0c11502802c40300714100204c299207901540100c0090004880d400c0c070904d00c0070402c0100a00c0903103000c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 141406906 1250 141405656 141405701
    0x80a0902060a0f17040b0606070303150b0702090907030f0210021c0201020a02010b090603030703030b030703060e06011a13030b150402040305160b041802030c07140601170a03020c04050604 83
    0x203081200f80c6900d41000c1489135070800503c0e9038052040384190307841011a119036840d00100030458100200070307002c00d0740d1135240780070705003800087c0c401074142185401d44840d01d502c100044207800034075030340c002d400c1040c2c2080055035100310311000542c111040c104664510108070310300207250072080744111840c0c1c00c80054540650042503c06100c1d03000f4042000c000040c010408401d40741160554420000030010a11961082a412000409a03422541c0c0d944550701524007650442d01f0700d4001e9001004040d60b1491040b20308081d00c0c1c4c101d03041141c5440301b180d41c0003542c40041d0500c500500090801d070300b25603581c04019030052085480340d41342e08083d507a4084100c03050000c41581c1c40c020550600c542c06a4003240c0c00e000300d1142000d809a0303400c0c044e420244c00341c0300103042448010001006c2680708924110f91500900d100d625003110380c2016101b910310b500190b0080400000841e90104400405060070344010825440705004140200640f045401150581450 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 141408156 1250 141406906 141406927
    0x10b090f18010801050105010f0c060c0c05060f1e04050c040f020f0408100b0111060109090f02150a080718050f0a0512030a020d0504230a0902030a0204061805030706080a090206 78
    0x1a42e060f100000004c0141d0780c3c8a0006407281e48a00d02108046283c801c0302c1400244150085c6a0f0060585041080c204203550340e0341c5460415280ca1700580724407410071034940810030411403c000f02c0c608041003410181c41d2245c0710560001c40d10f014039181c0c2e0f804c4100c804240c0440d00903010451100f81d0f1960390380012501c8007500d184100200c0e041107005103003507204620030312a140915000d0300841e481e0002c0c8400508070b03034104580255100c0c0d500c4000d641d0303480c84040307000703120020181d0301c0168000081c40c0507002080c80b010700481507102540144603800c01d5080e030b0b80070f5900c1480c88984000040b12728042e40e0050740e00034070305901d00c48000e2022018248242841d001c4641764401c8000984040c040d902075903844690f0004042800c0140d010700c0d41040c040a48160000c0343c5925844050f6032040350000880d6400080400032194015460454802c0369400840f15600b0a0000b036200d01041c40b58004020352000801c0d40c104850348a441c850340d008000795a291011231 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 141409406 1250 141408156 141408199
    0x11150709030c090b0f240304060b010305060a062007080a1a180c090406090606090b12071a0a1419030f020c060109020c0c0414010302090c0c06010b090f 67
    0x700702e4005480050004002d60303107000e0459006801000000c5450340d410038020444170500711030380070503a00000722400b000140000c5000700d01038080801c080d55580300260503200081c0000340920b41402c1d0400c201a8490420201070a040041140f0105d095003502d2901ea0f041c5c100041d103000304401c0008100c8042e80c4985084c64251941e54607980b00341e8980002d402039902d07001c181c3c00c80380c1c0f049054a454038482d603105120f00700000f100b01140d1180c404072840768102c480746a0351810a580790f03262007447c0d4070325040c91400a00c02c0c681020703070540d00940d13410540b1210700004a29020302c5402980001034680f5611103030750b1a9040b4080c04110404034500310000300e80f400d40740c20f800742641d0084a200c2c03a2040018201e5910f00645040254846100c18503e4014640c21032110360351400303507180000b000400395009504500401041d9407004d0812495004200311401241101040460456151080c03c9442e00e07202d0740400c08041042a10581c002c00340c140f881040c04a01 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 141410656 1250 141409406 141409409
    0x3140603060f040209180f0f011508070506070f1a061c2d1b0e0106110d0f090801060b0d0e030c1b0102031c0e010b03070f090f06080102040602330711150709 69
    0x50000740700c105524044c540cac00031032a000d0ba0015401510040c012401d0020081c0704003031141d1440a002c00d059282d062001c0592541d01c2402c942c0300090142c203160182100541d050046001044560640d0340d80d101c05c1115400310510030402800c015850011700301c0c0c0c5004581091880d9900c000c00c0c0954004403d03a401551038410345034002062441c031504140c0200301d42c2d14020310803c000400180d4a03860700010000821940e40d0011605020a01031140240722810986407603860100444041d50241c1504104550040c42000100c0d80c00045008ea103000701e4801c00d02001d00d8000403403c0d8443c0d1b038070009040d030b804403110000f98001e0b4041702110032404000c01103441703070b00105611000c26105e01d6407030f00806003042c40121401d030300400e901001c0c1d403c0000e25643d249001401ea800079444000960171580c48200d0303030f00200d8a034010b08030a141c1c0c03260b0014038083d880003103144080c00c80c3d0304003c3d0280b080c110394802000901c681c0312100ca1050002d03e072800008180ca4000d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 141411906 1250 141410656 141410683
    0xd05150405070206040b070807080121021207030201090b070b0105010807170412020f010911010509041b03140f0603031c090f0804050307080c030318011403040303140603060f040209180f 82
    0x250004054a11407100c482c0245019910ad102a1346070481c4281140b07201002c0304c100e0180702481c03500607903c0f212507070302c0d24101802509549265000251410000b5030000301684420442c0c0000512440100f40c1503070402d007007600791a02c80aa085801041000380e07290094030310810320040c892045882c0d0070f4030a159003250310a03400c581059080e00c0360540001c1000d407088404407255070080014201d0b00d80007600015140100e0301c44030004003900c0f0b5580010a503200040d84040c01510b80c1954800e1300c0b820141c80d03604003500420350301d00c00d8884040321400780146031051400190007100c00c16400194103000710140382001141035001e485aa4032920804900041c000340100c0d541d015050000c0145007401a00075044461600c07202c020341c10400c851348181480c0d403180f0055402140a44e82c0000da1005038ac201410303003600a031203103220b07500a8042100c0c13080141c0100d40c0c06681a00c00d60300c2a01c8445041c4078002507100c5c8200d0601940b101c41200c03050000782c8000c410031 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 141413156 1250 141411906 141411923
    0x30912050109210c0b0702030f12070f14040905102c161407080f0406080a15120f08090604030605041b030c0303030c09270c140d0515040507020604 65
    0x100c3d00f1284405103074031182c001160800760350002103030903180040e500042e2801564501a03519010a1070703940b001a150003010119400d100c140c0ea400201c04070756500500303100591400c050094029030089204841c80a0740390000248000c4c1128807020040111030440c0c410700b9100d8428600010f44a5000380040510304006100d900304000580181c1ca03003030312085107030a40c0c0d0700207400c5944104401c0c1c60006040001d0102c0c510000001d000801e980e603648000780c02c2c070705070b12400e4811003010898411804001030210b070f4107402850b81e0f1282d0003043d00c18003410914100c48a03009240855a22000202d000420700c6482e410041c402c1e4402c51003042100b82c94190842d100e0401e00014112510084003800024006e510002c203426442c10464040360340e440c445003400407040318089640340001c030510101c2c002401910b90401c01400e00d070004500640c80308101c0d002c0e08400d40c407450b84442c00304400700c00341190a045030802038024080c9240805010390b40c0d05041c1d8040b0390800c2d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 141414406 1250 141413156 141413183
    0x16090b010215010b0d09020d1209031101020105071b050a0605010617090d0c031209020405041101030f0b090a02071103061317090306070f0e131a030303060f0d030912050109 76
    0x140391807281c5041c0c2d2604000c19042c821659400e10017070106c038800701d810400000709107001c90400d60781031840c82c0a55454a13030040c11403502c030324116915102c05055a0514050103001030f000a40c008640740811040c280107505814418540144c844002e032015203020001305119034010062042c0f1a04220103824a40354500b40d80e41c0c95142410b0040056141240701c8002817180d01070000c08050700300042102c7c106a000281180c80a0740c2c11242002c01c441100004d581502520f0511641000d082146000700d00104900364002801d01900940c0001d50404000c00340e00015603c210180846a007031906e030107003410018806c2000e403506241e01d81d4841c5889044d00448611900c098090413080e200c500f020740d00c00160310b140c0c5061042003451103045441c0c0706001e103141c80d020500826240d14900d0f095102c01c012001d0300d400780d002041006680e0f21601c0321014000000d0f2880c10a034100d60a04883d42e603490380011404200b0f0079441800c5c0078054103c5442d03039000e207030040c9140 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 141415656 1250 141414406 141414433
    0x50303060111031e1b010f0b011d090105060d02040b030a09020a0b040b0f1b06070e01110d05041206020906040605120703051905040305040b0c031e210916090b0102 72
    0x240100c0d40000f060003c007044913401c64031210040c101d403456030501c4c412079200ea03800450940c0ca280a071401040c1d52070301d0521141da805101031040000020240508045020100704440030501030540035074000985d459500c0440d80c1228001c00306480056280d00b811041c00025148001c03040c0c0c4600c051303103400b04500181c038044070104c0794201543e91611403100b503502c1d8141c000641024007500c061b000340701e4100040c0211440342006544480d001e4807044005001100350074103000390b40c0d0103c000c00c004150000210380a035809201c20011030803270b41c80d20b503000c0c1c85041030f025004080881c3c0018403641040280c410b49a40440201466407001c03001c400301c4008490b0035400c00c001200c00325404000360b00c03c3c0d42140c02071070124900750300c880204015600008c6800d13801d6000140030280081c0d0326100d1b0500c203c013900b41c10f250058000c045048041d05990500e8801108008904208000c000e8480014441111003c0301a5222219801410054080c0340503005003010040f24 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 141416906 1250 141415656 141415663
    0x4050c1905160c1e08060f06060d091203061403070e04060b1c0309061803030c020112020a0e0f0603062d191401080403020d0c0204020909131502090a030618020d050303060111 77
    0x10303220200000c286d59643c0c5001a03c4406c2c018200f00d400a1b81040800d400f01c03142d00450500c6070040b03c035501348004440d401800c9502c940d20510400c442d80441c8101940e01103246400c880300d2685070107150310b50382000d00c010052010f00c2c0768001e0400b8000800c0044100d180c1c103915011f5194031141e80e6440d0dd007501d0703071099007000560320070044000b4030002c0d0103801c41803c203e0040c941500b00c048a218420100c0e40103074060400308040c400f50190758a020103031200d4080007070b5212420b50400c00040b681c1d103000310f900407450004101861840d101181600c001d041d10062210305103640040640d29145414003805c6203582c40d00007802425401100103d0140e44e059000f01f10b5030600c80030403164090540012640990208403034007071030b914929803d0081010010070002000b26107001181d244004000c00c14260060140004030780c1c0f100c059804880d0400b0010480c180400418699000803450082d40f003124001046c040c0308001018502c01d2800b0b0f05c421107082c8072200b10780c3d43d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 141418156 1250 141416906 141416909
    0xf14090a0e09070e0c16080309150f1006050c0a06050613021603030b0102150a0c02010b0d0c15080411090a0b0d050a0201032d1805030c01050906010504050c1905160c1e 74
    0x40c1d10741b544100c2800210260000d60b8401d41c0002900c64000c1d03034003007174a480f0740280c480c40391200d00c0d641408a003a01d01e0380300f08010309a030b0400e1803500c0c2c0c203001400e8891a8403c009080c05a540c00020070544034030f500c032007007400002d0045554a1940b0078143e400c21a541e801c1e00041c1ca4100b0440702540000b4482250490191060826607240c0e650240905522a0030000b1552201340034030300c5840d40c60b14022111712440000720303414103007a641160356685031040d03800c0000c04402c0c0004600f0541407045001350507074009800380d40301400c5402034920311075420f82042000449409209000c5540b54009100340d905005040704801c00168660500c00c00301207405800030b6a00b0034070150782c028605203000c210f43d039840e044241c13603181c1913802203844400c59944032803c00c03050324410b00c519409450708460412080c1015a03408286003e407000c07640741d540b81882401c0324203004406403015842504000c03e40440d0718981040d0300c00790b506c98208100314540a50740e11003031070901c1300c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 141419406 1250 141418156 141418177
    0x5060301210606090c080402030d030203010b030a0908070f0f120906051b150c0409061a09040c140c0304140405090c011b020429010f14090a0e09070e0c 67
    0x180c02a605500d007694600041c1c4003210384030355a01e40007451030f440740202101c40100f9211a0807a10741401811300305907011840f02d04061042006002b018100010349810207003940d000110441146000803480c810500e000d800c0c0491b090f0894104000180d0b80c181d081c0c07240b142d90010040205054450069500840c3c0c00b0480610000103010f0010050703c098503d40c500701c0700f500888005800040100781d41024681c0e20005d428041c0030381901030380c8010030020314030400c81c3e140003080500c140113082c44503106989a040d80b41042c3d20442c40c0c0c204051310101ca5581d41c0608407045a0340f544076101d00f0401c44803a40d2480300e11300d0030b07110300e034440c1c5a0034000e0019200d1005c01101e8807030351400e20015940310403045c0009601c0380d00c2240107009101a090540c00010406038900c000300f40d210130304011038180c0120f5160f40c040411503580d40b803c40160345840c1d01000041e00c206d000d81000002410f11780400014440c0051006d044036000508a402903d0b10b00a0403c0e5109002021 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 141420656 1250 141419406 141419429
    0x6030c0305040b0613020f030c0318070f060c0510050108010e0106091103010b280903060501081903030b0a09090f0605180d0e06091908060601170a0e0c2805060301 72
    0x5505017003e066140070502c0c650401490000d06501002d441c0c3c2041d2060103610a02100b000700010074030700d0000d103541e100340050000501d40702c00e5480c01c1074140904420851040341820800c001040030104d0310740350032018000c6684400440303000704a042011303002e542c20f0001c0010300c010144111042c44401c1c8811a1940c1e09002c1c41c0440d0b81e015480d10311030f0250302c5850045140306101c0320042d41080d5520300058034a10704105003501c506801909507604421751241c48800c0b41194111419818140401c0c880fa0410000342c10142c01d500c544120303410400c80e00d08106807034400c800002c0c45020100503a46998087c03480b0421014030844040c0e00c0286070001c221302030004801c41400040c400b91030a4841e4001c2042c4400103102d480008070075000902c02941d003801030540c050400c0c030381081001000c4030490384031180070782101d80a664400c0500c078130200c20301a000c0c400c0e001800d05285120907401d00690b0301c00285122200d201080000325442c94400e00301e034101c0b04c00c1d407081c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 141421906 1250 141420656 141420661
    0x5041a241903080d0b101416030212161703010b04090207170403081b030a021009050a0b04050f12071a07090816031406010602060115090308040b0406030c0305040b 72
    0xc1c8030001a9403900001100c081890000008400d18000c165030b111001d40410b03200c40901c148400100600581e0090001c0300010450380d4103650180c50104040304260405810b2504044c1d080403004000750940030000188005c0d904120004106005d201c0e426a15098813001c1c1c55185600003805010040c00041104201511841d006080110b026100c403203180442034045d074440354001d030310407158020003140e2254200c0102c5104501154800c01441c503203180090000d4442e8021020154402d9a44900c0010b208040201c0d079842c550098020041d070602e420440d565012800c1c0d120340718403c5d220b50f01d8941c0e072404103132000b2651105000d03000502801603541d941c0c40003041c90040020308040050810380800c20403408447c3d225820521a0440c204108040340101d00c088440c4d01900c010003200d940081e00c0b074110750f00c140317440401200f07c01c42101c442c4c4c0726500140011001050200d101a400001802201c0f00f684041104460b80d40381601918003c450250a680380c0c80e00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 141423156 1250 141421906 141421909
    0xc1e0f080415020315040e0c01090512101a0a06050c030a0f05070203150105030d0c020d0b0603100204080105060909210c01020f04090902010801080f1f06080105041a24 74
    0xc9422034070901c90555084504808041243c0080f120682d61040e59000008281420301c140140981703018007411000791290000790901030280310f10340c0915900c044084080b00c003405407034403040c1d0307505013402821040c104001840c40340d030307080303a01ca1044003000245441c041d00c11504284410070246040c03040d1410b0035541d0420301c142e42014008100060001079078148000c031b000d00c01c801d030458525410502403500c1c01114090703150920030100c0041c1c000da9500e00210300001d9004000012954851000ca41401281118424002d001240206403603906400c5141314003810b40d1100300741d64880043e50b0782d5030b426042802e42c1c81e41d2500c542d840040040000c080b2403800300d001501c2e0140c1030007441234541c07143e808140c3c529969607c81d0708641e400300b10306004240010007040080202c407219501c8103031071001856003400c0030703081c11081686900040700074680741000f048545001d05294090003461031013201044c840d10009040c3c000365601d401842c0c2101e0400c41c981c041c0c110f0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 141424406 1250 141423156 141423167
    0x50f0a0806070e0a1e0602160b090f03010b1e03010f02070f03140c1b09010603020a0206010e0a11070f020405240108090f120c12030106050d0207061508010c1e0f 71
    0x324007034100c25808804506224902400c030030110b850140800f09919046c0c0003402c0006e40a40d50f40004604407040201d00011007c6da50503a00440304480940101c0001034010640401040d0700a452400c0044040710001aa400710780d00aa0081c4092030110740c02c8012440b407008000e00c00300e03072240d0000120744640600b074140d05900c040350f403801c00072034074061404050480c03c6070300030a051244206400c050030300600404440c00e081d81044420100a0345034041400340514a410ee031000520150080d0800c108092011005e15602e2400e41001041c0842d0040b00743e0299042034003141c11400c0c01645d44a11000b080d0928100204d20001116400405011307141c0520801c60031015112050082100d4046500e68031540e401d03100d085113040001000704440c07002d00c1440100940d0341c019044801d100f081220044e600e5076545004001001c1807805041003e540b2100071030301e00360552204198030040d072907009042d179500000c52490050842e00f0b40c0001c4410b4070b0940403a0148 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 141425656 1250 141424406 141424427
    0x105040b04110102010605092d0402060a05030c071203060815060901050d1a09012007031202070227070929070c080d020303071707021c03060306020d06050f0a080607 73
    0x5200206e5030b6a6110006116038030162141f20f0109006000c40f2000302030100f00282d4081c001c980c4040d00d00e41900044c01c60700482e044c1c02c060050010009100409a00031203800700d07807000342401020700e0014014001c140c14052100148100007a0760040821000c280b4030610700104503984e503a00342030902c8014800c40804503003d140480035496611034a0004a02c1501c550000050342410035000c0c0c8007415051081c0c03a92208200846804039602410408181d0005000540d4030080c038804580c0b548003031032090f840602409840466031080c19801c5005d008030769604a409902d420428141000f40141c09030001c1300b2007010150369003000041c0a2060083c3c44d9109003e43d01c032551070410f13400308c0144005820010070801403a4000c00700324502c072900440d0004c1842d104002039500e180d20306141d1402840c2042e6088003d219403c03001c0a181e00120554071036810042c080054400341c0a541d21a04e80c8000344200c40c103128901d1011503032032900130046500c8516080c0d6914100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 141426906 1250 141425656 141425659
    0x12030b04020f040b12010512300c01061707050f040f0e0d050703020127171b030301031a040f0b1e01030308040501060f05030c06030a0615200105040b0411 68
    0x91054402070701840b00600014240600204e0b911428400e100a040c00141c0220b03114030701110315003d480d0000540c10002401c11120001c410391119561429100c02c25000201c80070300041d41c0304041411742000e030850380c080603108010000218841e0b1940b8083c02aa6008080381d003491a40d460030350001c00c61102c0700c910025000c0c000000140c10141030302480404940700148200400d942403003820f5462480078542d003001030707020102515003d4002c1000e441c0031340310098003424120700001c4980300489001a0300d1070b200b94658590700e075003092005860004500d0120100c0c00d081080586c4120f5205111489002440e50303400e10306407000d4881100152020b6001d49242e13060325829010f58001e84943d8840d240a141c01420f448a075049140405084007042040343c40020704e20040740022140551070b952030080da00c008004a60066a614611040280344130343c11000030610b003031403446003280f80180b0b082001c1c280c4005485c000d1400c0c10150003e40880c200540c030a000010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 141428156 1250 141426906 141426911
    0x3060b091005130b0408060f01060c120309031202040f030b132a0305062418161205181209130b0121061502011b181a0406030507020a12030b04 63
    0x102c40e00441c02c02d400036000704607141d100d1000c0c050548135410b0308d940180903c1c039200d200d4041c240e481c01d1030440448803441c24103480c7d040c4402014010b411428100c0e2510b0b071704540303a980e038056428070040a0b05c01a41e032201030101180000d24a4080c01d44000d4000244030402c035200d00749041003031200103540454046101011000400500400e8001e5482a401e00400001000f985020030034010b01e2600c1401c0803001c1c081c841c00561007150744100d07902403042440d101c1f1001501c00505c1d150f09840d44624100070000f0020707c10001c1500212610f080707691442040600b070b0038502c1400d0450f941310041d80c8401500500c81d811590241c0c0c1e0614092505110240c107504403814141d40081440c3e4aa40b410700034426404c1d2028225806480280000e81880d80c1c2c1a00b8880b40352546020001521100b0306200740050205d0010000c041009205c0701c03002466080c160810301072900060304000100300c1c0c5610014402e41c0340c0390080e00c91152a8400313142540180f00c0c82c44510f8010740c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 141429406 1250 141428156 141428159
    0x1612090906030602031005040b010804030806040b0405103b070306030501020c2107030e06030a090503070b070216050f1e100e1002061017100e0a020103060b09100513 73
    0x10103034020709006600c200405600ca0030076110030710007082941c01450096240054030f10a07070b030340b00c0d140c00d4100d5007602b07180070b803500c581e030119014060582d0587e800504100078030051542c03882c40d43c002c517000d1410701901c509941900098202c0599001c0000c0c1d02c8511070310842d800015000b0b6004201400c000418950b00c0c0e03500c40c03c1e030b08a1050407015400c02c4901d100500c0d0400d1200310a40102c1054510f03041a507034018145030072108086000e042c000c0000742e42296254030806c44550868112600c1d01c0e242c0ca00316654030021a00c03a0018040c51460002c000d03030050520055039401088409605c40e910140b143c0840c0c10303035002c0c010700b1601100c02003076112600d803101c501d00c40d542c80740215078028051000c21a84140010110f5001808000c508001101e902c404e40f10008050310814982d0f018403454008039040c0086003500d01280c035540c403200000d820700418401e8a0078403e040c2e84148440403806040b0b0465013090701440c621140910560060642c00200c84402d03160381d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 141430656 1250 141429406 141429419
    0x50d02100f030b131a01030509030409021818180d0804020904060b040e0a1a0c030103141f090203010b090114210706020109050f01020a020a14010b0405240105161209 73
    0x808900807900c2119034031000e401c0d01076607100c5042c001c91400e01f0244000c0c104105116a0b0348114821000f40d036030301240d0044040703851014000c581000401c1031500c00c04844541d21106025076810a13401c1c000340342186020070114000007840500d4603401300319030b640d80074004180700040c01103407419a9803105164540c0c0b544075804001d40c011008003100303012441d10b241c83d41c0110381c1038001c400c2003004000c4d03d12007510440e810360b9446410906e489401054842c9010801d501178400d41d0300580e06407049542139030000700c00b14001c4000b070241204210900031070550038083e2816504190340c404505080c80560000c0021485603445030340c0d8246912903007810865001040181d440342c1c00e460511a04000c0c000072485506c00031451300c062500040c1d81c0700050350f00240140484900721411030360a41c040252007101030000e1041e071504c2c1cac40d0071140c185240701e0003203055125000200203500c51030545219505224246a9499840d12016042000b01e040213041008423000410708 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 141431906 1250 141430656 141430669
    0x305040317090618010501080a020609130509010906060501030903020c06161401050906160801030f060609020d0c1407020d1419050703030206010b0306060316110318040501050d02100f030b 83
    0x160a800e0b003e0105801c18040201c01d0112540c0c0d46500c6030704180c0144649000480c0c0c0300c035660390403903110380e4840c80c1c10080b40a07550340c6282403101c40d2600d000c2000d060300c113400a59005214503810019075440708010760440d10603020160050b807000884071894100a802058003c040c0003141c034074001a43d455040800d01e0b5012801c00d82d4440c2c051000800381082569046110b01581900030303034041e00300811040c01480040c0ca00d440d5800b4950030b202059000d01d011b005908030035980d030303540c0d0401c5402030300c070358600c0c28005070364011107800320b0043c9425202a87d40c0144040203401054a40f5a003075116014034050501850440050140441007000310321407282016155041c0b4505019003448016401304030034403010000c00103265901c10440343d01006c4601c00300c07808201060b00310b40101040310840418400000c44c00d9207a4071030200b59401c0c107003c071014403060ba207031410f00c0384640241e84029001f0080403120044140203540e12082c0801707924000031400190f0000805 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 141433156 1250 141431906 141431911
    0x913180309030627120c1a100e010b090d02030309030703150c0c11060304050705031f1107030203040b0c0c04020d0207150b240904020403030509030d0c11010305040317 74
    0x4121848020010007956004801d130140040581400600303840c50009089210044010020044080003130b800f5170007840304000c007941080c0304010040400000120301c010075070b0504034a00c1c3c030210004200d0344807641181038a040c2d0a885d03041c0300c0b42d402886a05492010b00303da15000c02e1180d0141c60300c0401200006500544409800300b00806805040300e00f100d140a041120350003002002c20b0900034507850060040c0e44241da0f83c0c0e02c0e4200241807040035003043e6810701030010605085d009101104004a0702c291041108040b0f81c2c0d207260603807080341c40040258000380020800003526a001c1c241e000d103004d0a8400b400316604c0040c040382c2c001e00025040580c0414410207102101c41140003199000808000c45c0164000040d03e42c24022910100c900b82c00100c49688003030901500c248210203007055403155140e2402801c20b0f081700018900911507085440c907024442c166002809401580b42410400003600450180c00000c0c4150207010011035040042e4107070300040ad1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 141434406 1250 141433156 141433163
    0xa02030408150613050402060f07080706090305030709060c0507050d15090503130b070c050f010c0203061e10030f0803060a08030d0c09060512220c06030c180b091318 73
    0x543e01d070200800c075880501800c4002c14500e054100401620791b00c00300c038094040c1c80c03005901c1700d016281c00d5000d841480d0f00188070a040c03010307000c205600000994014030031521440c20244c0c644a00f00c41c081d0200c0e40141243e40b160108100c0d504000c000f0303907030b40b600034103140c5d825076000e0f0a0001035800c800000c44c0c5541c0009041840000540d00402c00303020b40c0850a032a0075120789850b042559503015291080e82c00e0f80007030074181c0c0100304061403a45e020f000c0c2c072801c1c80d04041c10b1040680300705096104101c4400000d00b8a03d04080c05026203511001c1d0340c0d01007403103403a180c07070700c2d00003d09043d000381d0420700c0402e5051f003c0015002070100500045204d035181c9100414280a41d4060310500605200302d503074042d10041e1569129800c884440101040c80100100c680e420358805805081d0f000d801207004c03035154100402c0308540c5d07207909498a155044441055081e442520b4038800280003510b950f240840f2100c40441c0054000718004c10301e00c0407100701d10040c80d401c5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 141435656 1250 141434406 141434443
    0x3010b030a330b0a210b030d0e04050a18031112040e071409010c030e030a210201060806040f020d03020a120207060e150301030201080a020708030a0c030e01200a02030408 75
    0xca8007a0b00c8104401c0251141c070b082c40d810080340c100007a000c011701d0009441052060074691000030401d6124014442c0700400315015131200e048040c10030013030200c00314090360410b400251190f0650188082510303120303002407096080e0b9101111001c42d4907040034124018801c100d04101d1541d0b0203480170b031001800d519118142441c0107414294a401c00304090300f4103100c0e11215a8000b15090303401900340c28400c0d4244880d0300020b0500f503003407500410900410100d02d00c0011038165101e40701030300b50000c0024945a0300300c10340c3c402c0100c4005140c060351414a8005041080100307110307611a0044805506807540c1d6246d00c104c20199400040c0c0c00500304102d0325510002000c02e086080e100e5030500000407e001540d03110500010741070042220101c0c90266196048500d103a400120761602c906212900c8800340030805c04120000b42404884021300c0c1d410310400c2c4500c03061100b07a008403948500d10b5807071a004114008150b0009100010b8003020034130010361503288a0071381 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 141436906 1250 141435656 141435731
    0xf07060f0e03011e1a0a030302010e12070c180e0a030503090d1112130305030408070504050f100612020c030c01060806070203071109061f0e090903090603010b030a 72
    0x910a03407001400340d10036070424201d40340414100c100300d10140c0c1075400101e80003100d000044030300701c00c0f40c3c41e440d00a01251400424554103511955404102406941c0b524400b4000e000c60350007108405010912000010030414002c0c81100204500d48071007c107a5510300d011607400c1140b003034825004544000104020b2520900c800040a402400c240101d070411040d1640d031040b8480140480301000190540c1c40d0358413042d060001c552040440355102e48540405855140903c07600703000700d0800c008070b9000c0030f081d8403152150b40780040c11a4510300c1e00004962001030046400c10055080040d028041742c00d20080140c5a06440003080300340c608403100d45891001881d410843d001805260005542182101402c0a0850301c2844644a42002440c025090443c40201090382c8920a000d02c0d0401e0b00e021041a0848001d105603840c1c0007101d0700c80c89110071895004004100500c030741026580616088042890001006c042071595046906d0080350140d800c0f801100c0d8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 141438156 1250 141436906 141436937
    0x3060504021303150606170703060e13050606060315100302040b040f0302121c0309030e06040e09060106020712030305150301020301080a051c080601050702030f010f0204051503100303110f0706 85
    0x242400d0070078440741c0170403c0600d4588000c00c400552a4188a880c0200010840d101d210b908440b02400034407030240c03030790f0802030303150080700200d074000712014000c1b4400100503203001e00590b031241510400c244407180c94403040040c0c441854a054062541c00d110100381c031030516019002400358207143c01e03c46030a40c010007100300c00004601c0c45075884074882c009810302d2200164220225401c0c080780c8103145140c150350f0800e000f5022500f003c0082000a00c2a11080c4254000c40c0c00c401500c0180c0d803079400032600d07500c030390041031301050061603c00c000034440d5100d42e038080da40c0b051000c08070440100081c01d83c0d100381d1120480e40d01c040c6040c01400b009101c42e880c0c80a104821100d11410090058043c1c8002001d01c1e05000012440078155181030260000640c0464001c118000076546018025006405014000c805c900e1140a4034444041141e020350b9940401d241d440703145550448201140702000e221601400c4600d684801e0100410000740c02540c0310881e0301c80390001c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 141439406 1250 141438156 141438173
    0x21c0536040b0f060415030e060a1a030c01081f05030307030c020907050315010c05030904051f050301060f1e1701050106030506031f1a0306090c010f2a0303060504021303 75
    0x1400600c60354001c03d848100d90303a400700b194101c5048041070751000c6080c5c50b040d001011114000d1f012030190804225100c60141d208120500e84250701a80c400019014142d60f40d1450314840d005c5007181e000300700540c02585a8a403c8805070650b540a00e4549010a055800401c0200c0202d443e15801604504c0c1915a41c0e50100e240c1c0361240c1503103001c030751010014201040c03981c10700080c00c9180c0b0038031409004950300644007910a21150510301809154000c0e1306400d40e00340a02040c001c0351914041c0605000c03903200e600c410000604003240150010a591040ca24901c40708500151007503203400290103061400c0d00008a0b58504040a02070307070300c0101058441d802000c000b02250304012100b1503522807094000800703034100f8203070310121950031120541c14800c110402c420003200041000390903400382da4845200305440000c8d03c00c19070580500800f2109038000780183c486400c48401410700a01d4041041603941021904036031003403040e90800d111850b01031051000301e8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 141440656 1250 141439406 141439421
    0x1021206030a210e091006020609010b090114030a020901030302010b01030b06040302130f0f020c0a02130b01020601031e060507080405070b04061205040203160b03090d021c053604 79
    0x1e50140810340d41ca581c80c41d9034802280726a0311001c10ba2800055110321440c907181e02d2030381c05030030a40f20742482d055451180900d8404c0d03000601c640300c0010300d40d0506005100b52003001414032041d903424040718403218602d00c0c40858040c41000b0400c809681e031284207900841c0a900001088441d02c80018140c41a182140f40510030800040006807515011460a80c00f11103000405508036140320740507112507401154101d0010600c40801480481c155240601c210351011400c054501d1036010f54405802c40c9000d0782004004102082c0e000d210380040c02c44035200e42601602d66034503502150001c1d40c1050005840c0d5041008101c0308105000203061160348881c101854004001c042c014285001218075855002080854034101b0a031040d21014401c100701594482540400c03503041200d501032207210b015030400c21b031400403418203505417500c6900e1143d41180e20b41540c242d8000300031155103070616110103200f290b0412120005035095030316203038404180310410082d034481 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 141441906 1250 141440656 141440659
    0xc08070501090302100f020c03011e0b150715090c0f210c0b0f04030503040e10090e070e07020c280b13090b01050d02070f060f050411060915070501021206 68
    0x42e40020303c0582d07601d140d0b40c000c0158928040e00d588624800482c204850011003d41660820b40d11138043d100c800011982070080300fa04100e212016070420121081204c0c892100200400545011440d42d40745040c840d013200e580400c0d155a80c6d580d001c2a84540e6020800c551000c2c84140800d00040c00c22014084102d808403002c59215100c2403510001c074460400c601c02e0004191a1203001c503400d90f0025500302c004d480e1a203980d0701c902911311804840080070382020200100f00c50400740710751011000c1d98402400280d0526509a050007005000b000c00c0d4801c074480c154060766820810b5000040d066040d10030054048000307094100a07030415540c1c0117090091060640100e00d10904807000f154010034450400c00041e60b07144101c04100b88118000140c0a0a21030242e01c2c805005109440c10800c1c1b400c002c1001c001c403101a180104030504030400c0c24a03d19001c4040c0041c2c10006240c1080444c100c0c4074406290710050301140c042e500460102c130758078000e060f0380b03030310120 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 141443156 1250 141441906 141441917
    0x3040501120b0a171e010c032304120c05010c09051201020702090606070318080d021b030303040b0402040e25051002030a05070602040506160c210213090506040c08070501 75
    0x5000001076401c0f0100d0040146940c2040e00c90507618004002c40710345040301d0b041c0e11008170402c00c2e005000c0c1c032000a415000c41d00300440d030804858481c641042d4403010303c1080b602c40d1030b1030303483d03d20001030b01c2090400c10442c0c01c1810081002807083d540034540380e807203103082030f4904000e01c5006c00940c3c0c0080501d0744140304600150301c841d0f40881e404401124242e669145d540740907142400c4902412116070000400032990310b100040401c20381d240b40d001c0b1910b0403142c1d0300d480400c4440c00102901030b00f0502c007050003e54500c15650b002480100042802e505042840d0b190503078501c640c1c441001902240c608182180c0001d0000e003038240e40403240700b4045c04000e0b64130300c1441c4190042140001d1071200303000113035066030301600005100c241d4503113110070810b5024400500c180c0380412540f10001d0703041107015681a454542c90140e1001400715020800310300c01c040c5210351139170380b2400400c0008101340b192a00c1544100c7c48030310080e00b0481031700d2501030280c1103d8188003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 141444406 1250 141443156 141443171
    0x1502010f02040518040f1a01060801091e1a120703030806040504020102030304031b0b070e130b0f270a021209150f07020c0a0602011a01031b080402210304050112 71
    0x4031182c84451102d09903510004e065111481d0100c0c1914440070007600560f5402082d04011179440b90241c125007060751060026602d41050208684100341140340180104041d1811180b441d040090010400041605c1c00706070b1002081c08071844a07100e2038590000e4100b0f004040e0480d011f150411403d48003004a8034040d40040c1d500d20001e4000740c1030001d440d0056900c0c03410500c82404284d401a1150f00c54104110080c0ca00d000b444803252081c03018a9038801e62240c2c1e88107160089800a18000404042e04107110030540503251780440180c1110098208288003031100e400740340907032001aa0b800201c1c90503941400060b020340d00c0d83c0c00c414a40c3c00350100408026401200c0035400e14050745842d80c1c180e103080d000c10a2241c009d010800000340180d010361040c030354448290076060880c512000110200d0790305188030038405030200c403800702c9640b250b482641c2c41407014040f10000480344d80c0c0161206103c800c1d900b840d41c0f0004042c4180e5a001d0301d000b41801e16007a040c450b48 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 141445656 1250 141444406 141444409
    0xc030303070e0a08010207080d0b06070c05060d1118040e0d0f0503100e04030f03050a0c12110c03040b0406020106140612060f0d0501060f08031218010f02041502010f020405 76
    0x30300c00903240c0e1040295407001012540e03500c01d1a00000c080c414001c56483c0700d2854210600d400c0100c0e00712625140201103181c5007801c100325140258000c0c1802c0f50b640c1403204000e025003180b601c006038250340721081e034001e070102c0f0018000034a803032400c50314560102d020041607510741f02c5401519085000ea000f030351a00003604042da021035003469a207940c1c40d4030043c0702c042c905920502c500301c1040c0502c81270640102c3c90710100c00c102e94003401140e5602c3c8181080d20b040c00b04140005114600020302c21440b540a101c0445e104c42a09192003a828102d9185420503042009a4000082d040140ca0340912075140104054034262540250003400a1494001d40d03000c0d1740001241000507004e6074030080403480d10030004000381c10540031811301d940240030a004001625001d0407001c1909880042a214048201c050003071103640e888466040a059001c0c0e42c51040d03407903028180d540c40304e42c00035001034451524203032941c0b222940020b003580c1000300d0b511059481040248010b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 141446906 1250 141445656 141445663
    0xc0308070f0219030503060a0905060a060513080a081201090b13230112050c03010902030d12060e04031101050601080103110114090d060204031202030306130b030a06051008010e0c03 80
    0xc04054140a520018070840503410b041082c481941d4407540e040400b820103800101460003401c003503800b440d0041c0ca03004a0b40c1140c1050315441d5025400307140030403200b407054006054141600c220030650030741c0d8142e8035103045d90005045805213000b0031340500d11554041d003d401801c007854188001e99048000c80d00c120050300181240c03603240d114224440c6d04949502c005081c0c2d48011341010b6035182900d079010008030710200c4050141203e40c10991405000f900203554004019104e820848042503440700d2407408000d0350315441d9580011503403502209148a503011b034848102181c0c2c00c049807401c40c0c070010035890522280700d00600200e2004114078080c00001c0c07c14450080c418000076905014240c52142d001c0b413180c00780800c200003034019004480c85402580208001010f050340c4038002141e0207500000320030f072195200e02d140d4210f50146c0700050306039112541c1b1a1100340942e40c00f105c8050151a10610070008a90248103418103403110f000a04030f41e5200d140002d44 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 141448156 1250 141446906 141446911
    0x3150f041103010e0f030d1107110904020a03060606030b040501060f0206240301051e09070324180b16090e0109020d1e0506010905040905030703140c071409070c0308 73
    0x10038401c1801c901e0549095001d905114555021565200590000f0959943c003134034422003160b05152404024854040030380308080c4d8005612070f0842034003414070407020b00080051f0ba12421802c400400300b01a0b10482000e400c00383d50200e508000310062009941060340310f0344c100b2005540144405d603011070040c0c0c100340c1c4045d0603140341c40440348070324200440504482d803551900701804201e50000e000c420705a0885000c11507a0395625119a81380c400621000e081031010f201c480394040b15101710b26841400d0b026000640c1d04582442e200382680d1b048084814180c020248003510303892920303403140c0c65020714098102c1420018440e003004030610070441425000306034501007200070b4015003140c2c40d1300350718144100c1880e50030402030442510001d0104544050120f0316041034080c0c0c150858002008603c2c00d01503640449448006400ca1002d00c0024400d00480710028000ba40c001c1103400b181a607810310040800036414009440b000c1804101c002e0840040d800c41c02c40c5030b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 141449406 1250 141448156 141448163
    0xd0206030a090606050a0807090c080601270e070c02090a02090609060318030703090e070305060612060409210306080d0f0c0c0b070b010905161407081c020903150f04 73
    0xe00720b01074542100030b00025049198003060307861001c92644800902d034001c4603481001403202802d171600a41d5646419522640012420403010201c270a12030701e2900078605483c0c4408480790785001d00d00c0780700c50580f241000510054489030962809a001c1034100124076401c501c4c1c01302d00d1000400a01c00d44220318090100440040d00c05024050403c2c82c821004003078941d12412880e0090810b500c074010041200c9901020a644501c03905c01c4511444014064518007a00003140c05603c2c20300400450f0300c01e031100c580030006000440d4201d03034110505180c142580600c44050151001030f04640010b6005585000441d940080c17a42850442414406481c00a03818034540e0250340703030440f003c4017030001800c40402c00002d01280c100c0700d0a0404010036141d907102d1424040d0b213100030a00284000820058040783d000007022000c0c882c4400914001c032103c465071480001c8910303c55040d5012810005600741070181c0a1007043d96034404015142c101986c0c101c24038080c0015 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 141450656 1250 141449406 141449411
    0x12705010c111201150e090703140c030f030409063f1703040b130314030705090414060301140108100f11030f01051003060815040816050106140d0206030a 68
    0x600b44401c070402c1184002020304000e821521a425a41c041d082c3d859540b58800b01c01040082c18005454886004a840a0107089480d182d5103aa100100075522030001c540200c0b07010345d001b99020010300c0c00d0034040320080c5465510303183d0300b5800c0b2412644003c41d03041c01c5000c010820020099813030b10644003011003e5600d141c1017201c0556002021f801007034011515040d41e40e003100b00c4d015510540c480c2c000180e144d524030000c1c1e10480342c40a0700070007088007115403403c2611114061644480d403407401d00e040c48040300029040e504400c08006101a48400740400c5003002c0c05051880c2d208840050f050354500082c855955a41d000c030340409503500c3c030105100d041c2070b4000c12008041060712a1310bd04101340c902400c0e800a00c42c19104080c0c44e0844081203008e801210125030500000d010401d85142c0603904250005004980300c010800138880241001108a4901805140006406c600f0300c942e14050700c0314000c00b284122140c00320600141d8684044a5000b276084070701 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 141451906 1250 141450656 141450677
    0x1141602011802101103030f0f100522180602030f06040605061207050403060f0b01030c03050705070201080402120610060f050403021302070204090209011d0a0e0715050f0301060c0201270501 84
    0x403101ca0f00c400300c1700c55050200200380410502d4024502e40505030301160101031b45c48619111001840e98801e1940040c050050420383c2c6c1c0321064900b0740e00c81302402c0402c528010030600303407000c842c81100b100c6c4a42e0102c14010005039181c125a48188181e070208129070504002500c14091440c1c400809601040018440b520643c03d0710000c503801201440803040744c100b010702424501a00740d0000340b809403841c050b21f00c00c1c003515008040ea034441603e403050640046800d54401801a03030000003d400c02001081d082254912a00740401e030103a0701d5090035801440d049490081d0410001c0500c414000340e0780301c1301c0c0f400340002e403154016680e100030310128028012a41001c1e50120600c00006001074252607040c0e244c45207012440100d80e501580c03070085a0819081e8113071a4003042d01842284041513109554600c2d50800ca400c100070413566141542c4240c202400007207045094204550300059540569100100039000344402c00c140104401110f1040300c4c1042191500c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 141453156 1250 141451906 141451939
    0xf0f0613020d1406040c05010f0906140c1221010b040506030a0e010f1e06050d050c011b05060406090209011508220507030c1d0f012601141602011802 66
    0x4007400d00d0500303000d444c940c0c40c00d030801c40701c00b0829111303050220310b15100403030b1014400d114203c1900c0241c1c0791080c007502140100c0c0040e40128200103020f1007445550000060030101030000481030202002d4900d00c100c1200a45d5101030780700040c000342c2840b00340159034420007600d500102441d000540c0c411801c04080c050a07a0300081e8605515104403120019036596062240941040003401401e64030014008034500b80600500740da006440189a07031343c0b040700034400c4449000451407143c1c42c240c459a04011042c0c1b02160b401c1d9032002c00b541181041c0003051b00400142c100c1c2d0034400c0201c01c0c09013124030001c00d040301d1070300c4007026000c0341003d4004000c8643d8000044401c0756450b46880e0038041014014840b207103c1c0314580742c1c204030702408207e124030103850030070401c2e92070080444c03014007001020725030603c900e800c0c01207505070034418000d1240d11074503043c1781c9080c852034518808542036405411a41014030034455404910020301403694155074040b1280207104 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 141454406 1250 141453156 141453173
    0xd020d140909040c080706110a0632041e0201020c28090b0901050103020c0303040b040c180e060901060b18181611010204210804170f0c030307020a090207050c060c0f0f0613020d 78
    0x400bc011804071341c62545002c0c9003158405104601c2a8240c942c00d45c2107810594050090312030090059011206c08a0a0708041c04000d5040d04030301019168541030300c0000141c1e44640c1c0100140c3c0c1d40d02c100844491500c0b0046500520b001c0c00c0c21803401044120f00c0e6287d03c4010809445540c884011034100701003401c082c401001003410307014040c001a91884003030022100b0401e0184108008165114018490b90b01180c81118920f03141914440b00c150440000d400301aa1040741414002800074030710019500c10041d80c048180700041080d0080c04886542c10082e015a10500061000a003c121070003030b44190b008040c0c141e8241450726440502c078580001c14409803600385140e001d10005800ba28078a80c41c000c0d00c585031850b42c28103941e030081d010003039031151502d007082014201d04e90040c51128014001d842c0d510482c2c0b000700384103a1028420301c482d580f101c0310b0b0184100e014000c510441c000c0b14045d1040b410007801141070b00d050080080d20400d0700211003000c004c1d030761 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 141455656 1250 141454406 141454451
    0x2010c060b2d0916050a11070f12020424050f13090f0c0803031005040504050102190513091803030c1808030403060c020d020d140909040c080706110a06 67
    0xb40d02c00322404003501c0c01654103a9403280ba01d4080e1288201140c1d920250498504003c051682c0340d43c2444416601150300680c0b011010030300703018001c0c000c1481103034080314401425140c6503455218071a80b040c40100d45441d030900d17100500e0610700c4001001c25001741c008031101181c4881800c3e00303980c0000d0040ba000300911920911305880a41040000e409410303c181c081e002090126668140181c0c070792004070784900804e02d0026080c40b2a180030b03401150400d0141c0d00041c10000ba8642189601c0440340400001c10703804240c2181c810045460031002e0040141c0500145501d03204012409005d0003000303084c5911405a41e15080c40f54000209020f0359030040302d842961000096100d5000d0701003510b641c0d041c2141c2c98191800014108403441d21503006207581d100e13280c4c0c00c5490303490440846554030020415100140c0d101c1503100c1c0502c6c01111186001417600d902d080c40d020b210f901090a2004001e851992503c0224803000c009030442c4000c00c503007a0484281c1e0054110 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 141456906 1250 141455656 141455689
    0x60c12051c050f060109060804030c17091207090c020109020a0527010b0d0b042c032b060f0503030a1412010311010206060906030a0f06060b071202060106080402010c060b 75
    0xb48420403200f400b0308254903025070b5082c0c0702d401c80c80352211400c1380d4050048401601041050301d810303001035581003c6201e9516110003490400c1640303000141c14071400200d010351540090014442c0f008980700d82400842a0300003040340c1314055011411101a610525105100604400c2614080039004900101001040c440151303151421030409800200540039801d00d03201d0380c0c0e12642060b10034400a8803928840720080c00c055050a44102800040b4800c180010f014407000882007414030344203130714034804001700c0421600221044900b43e912000c003490100d60308101d00e480100c00c542a11103180fa1401c22020b26400c1c0504ad0320038451011100c56194000100b8440001c2020f0301403802642500c1150700c51404104141d1010b0b1440c40d41a00f0101c10329000450360480c0402013485814003103140c50b5920395080054110b080152442c040b540c3d60f0b5103c2a44c107024040c0580400d080c0b07910300d4142500001e10000c86481e00038a459620b041141c85680d41e4026114103902 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 141458156 1250 141456906 141456911
    0x305060d080703080f07140322060203010801330501140f180f040603081c1d03041502060106080408070618030513050609060306091b0d0501030c060c12051c 69
    0xe40303401044e41d2822103512401d20034403801708200510485000b0a5180350510585c02d58603001e07015001180000c3c0402e40550280b108407001032860700282d8024025040002003c00c0d020061070300302007200c0b030413203010862038082110003018041c618066507001e10707104095503039400301504a0b108104000100300c00c080b03007090075140e03281c103003444020041e034410300c2401604003804103030b9210b404001e180f007605001880da0352070762400d800d8503440b4210002c40d0594038500740a008018031010450146c00014090085051030003222010582d144024a82ca600d490070043c00114007030b000601070500000c0090502c03140d50018814002ea407004000a03007040e00d40500164010744482000103c1d208000a5602d00f150030b903410104041d01003442c1d0755800c41005800c441c02082c401c010a801500d03c807869800c0301c082c01c100005010002500e50450401890000c0e003030f440b6104202c17207c04101c00043e01c900c020408000c240c2404d544960f4040412407200307031492200d040b00303032 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 141459406 1250 141458156 141458167
    0x30a0b0406050a0c02030a0806060a09050405012603040f03021519030b01020c0105090a0512030c0601120605010e0403050a0c0c080f014502010507060c02100b030706020d0305060d08 80
    0x2450b9442a401945110350401062041d854141e07100d000760a241c0c401714080d4000120701d030401c0f100a029294091070a107804030785070300018044034800c1e0403004036010420b28400b0002c060091403002010460006e50038180b4015100039a9003003800000e024a5108800d0189850101c0541d00c100e180054000e01c104407210000b0003d0041488841c014441d506500d202940188200c5107202d0025111842035801c04c000e110186100b0300010015110410001020810601c2141d020300030414903000c000280381400320a0724010303007104080154050902c00082c5d0080102d414080c130b03600b0304281048a82c00c081c5c104400035444034849020f409042003100c6810350007481071044034603540381400380d25030320001c047c034040328800700c0041201d41c01c1e0401180782d85811581841490a1032801c2103540d5004151402c40081c0e0300540d01c24170b900200d01600380601008040c06500501600b032410000a41e11500195580241030ba03c0000c540c5a44a4002d0000043e403c544d245036140c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 141460656 1250 141459406 141459413
    0x902060403060e0c10020c01031a03030a050304140106120605070c020901180509010606050304081308010f1a0117061009030212060f0108060103051b01020a0605010312030617030301060e030a0b04 86
    0xf058507090b10390090054200f070381694a00305441648400103a802864101507580040d001440c9185101d80d0403003a002c0c8100e56990100003c000c10030803a610a5120304080c5007002850b101e015115400340d05109090208000341c4a0240c040c60b00090042800d4070f50510586e50f150781d100000e50014001800414400025500c003030345030300d0360b0b030081180e03070b40d0981424200d4841d07000d40e8001030000c0001c030b4003266130440035055182d4440300c2c202c55150781d64005800c65084c02c03d0060b1594585502c6040401d1480e0400e4280c5001c0c00d108a100003502e20607050910000d02c4644509003540841900301d114030040d1002d90750103800e040c021029200c0c500d03654401200d07032015032080c1c0c800200740c1040102e8440c0c1202d900800400700c41d00b04c180f88000070305000d40c6050441c42001c003018080b03802401401c2c000c5004900380341701d0500c02400181510402d802c20301c0ca020301081c40000300040082202e0465503289001034501c00280f00080c1001b03810400941545070100901051 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 141461906 1250 141460656 141460661
    0x60607081b03030603281b091505010e03030a120f180503280c030302180d030e031002041208031302060c0c1903020603310b0610090522090206040306 66
    0x54441201203c0d00c0c5410751008594134040c008a80e401d11b0b1000b000c210004003244201d4440400200b80c1c11400354403102940304540c44010012441c51a00508100c2540c00000f6126552000d8028526026810340f014010010024800c2c01445d904c070461100005254807400b1041030002090310b407900c084c1012a0349800c082c1c60b01403100c3d040c12400103c211070352001d0501c205030b03840781d2500e0411510168029044407500c04114010031402c803060b070703a41c1c1541005043c803903103030b00c203141400105040c50400200c0c259880300d40704000c140918004880b0214440e80d200c0c0303046d503036961080300c181035509c1c08100080d001400803030b41d00503224000c103102d9081c1e8010b0301d80c21040b070240c2c1c1d400c0d00800600e00c0042d4019400b003000c241c0082248074034065102070503e034000b02d04440180342c881840204000c2c1c40765981c0d00e041c00f141d460a1210114002c8003890412030244c1070100240da100900e00c2442c01400170100d03181d09410304d03a00000c0845400420031900c50f5500d0900710003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 141463156 1250 141461906 141461911
    0x120c060e0a050309150c061504180f0311010203240402090607030518040b010e060a110d1101050c030411010c031211040305010b040c080a0c0e0409050c03060903040b03060607081b0303 81
    0xc54940713148101c641c52064000d80b80b11001200040100b40c48408e603501c84052880348158206403104048421045618000c08110384520821142d0480500700284080440d10754032403640d004006218050310a18155051404000000c403d031703d10900000d4020306c035100c003d58202c43c001c603580e0b0505401c031024280288400384040310018244080104468180304010b0114004076040b08c12824036002500b481481d41c189410344503884501c4074940145042c083c000180c000790f941e050703a1002e0040175081240010402e05508080d564004d0161030010018100100e85000c0d0051500c21005448041290681003040c94444000c098180e806404251100e601700014542d6600f01407043c003072480e2141d95034442544802d0700e018090003400301d00c4004c07c42d40481e00300e003554951080d5009144074600030800d07d0640d1050608102c401044480c454005000804c6122030312000c40342e2003c01192000d07680c61b08e900d00307000310340900814005102c00600943e000c0000001c001c60 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 141464406 1250 141463156 141463159
    0xe0117070905010308070b04140604060507020c04050103110d05030d05010b0a030c020c090a050720060f090303010f03080d1e06030507171504020f03060a0506010e0a03120c060e0a050309 82
    0x6004035207a50314003060b0b4000f0302c4001c10800d07081121501080400d80c14035041449823100120850003909654540441582c050b914140e584041c41280360b010860b9040c0110162028401589035441e480103441c100f42c9914001c41c6070042e94010000140103c403d050b001c80010845561111030a81154001c40c401d080403d01d4032300a20703406800015400c0c03891500508040da5591924903010160401a2402d000d00004010003901d05204410700c100085003400280f060789080c410700c1d001d148020700001c0c101e801c01c0006000c940c810f9903c5500352604480403541d0b44c50342c0207c11005101c16081680141c80740002c0c402c1c1210035800c400100d9000d00c0445003180c1c0c440003034001d9081c01030300d80c0b4100d60095074241c01b1402200741b00796201e40003c00d80c190241c03404000c00d040403000c5038001c02c4142d81d00200500c0c0d607040103a02c8500325041d13940c0501c103030035a0746080c0c208250b00580710a002c140c11805080201a030091018480d1820071307910b14880ca4078169590343c0040c0d44c4035 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 141465656 1250 141464406 141464413
    0x41b08070f05030c0a0c030509220b0a05030303070503041a07030507180b090906040f140405060a0b06070209040c03050d11071401020303010312110d0807030507030c20070e0117 78
    0x1816511a10a990040c0d04001d18945407241090081d82c89030141b11040b4207000d070a200c1e408095035600401c2c4c003a1012000d1149a48003030015003c1203038140c00b5030324070036080300c58180241c0c0c50000070350b0b40c0301c031103800e10b00da480c2c540d4180410152840c10b6103500a403061740402c0041c50341900040c0c0180c41740d0b140c0a01418500031052401c4801c2d003d150041a802d1000054516141c29150f41051000d000022041d0002c0b18480c20f07604415103d102004c0c01c00188400c1010030000e043c0d00021840b03040055129a800045141c42030110191241c14144003140500407050781c03140003141d004c03089035100030802801401c07903d03200140b0060f500450030000744a4960140300c100d0920164007075032850382507507124440c80f038280c0041000c001040c1c21100f0035231130800900c0002e0b40e198607030312100d251000000301503070802044e1200705810046418070094012a01c5441060b04500b40015488550b00c01850480365a10041000c803104000007400e07804004001080e42c500300a4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 141466906 1250 141465656 141465677
    0x703030c0f022b05090d05070e0907061b110909060109060b030603070b0a0c0c0f051309050a02010f03020909010e070806010504060906050306040f02070302060121150b041b0807 78
    0x10303a240c89410120542c903008003d800d03140000a481490502401418520709220055000c00c1040e040010f080f503940d4041e680c140240808245041c0c0d0090000c8010040d0385d0034080000c1c149861400312560380391015440d9420416021951105e40c0c2000d0140314641c41e0500400366210720030312900074440e1600c03030042a0117100d001101d12665001d0002d00e00585406c00504942e488980c1480801c9a443c01940001d800c034045007004201000911f0b5105081c41d0030464552443c000f01a1001d107042c40d1500080c002103601e00c06143c0900701300d0100b5054010a50191207100c0352560300c10243c0d070000c142e44841e4110180903460a66500d101941c40301c0064070241300b02e0241001044402c002040554452001150322100c00380c004038241e058694810145d8110000440168002800500c4100c1c06000c039807414041e03140c1418221380e8503072a0305032119841c2154021140d125a07140c4107540741c80d00300c1a00200c100801c010554a1600014001c0805668400004080020 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 141468156 1250 141466906 141466937
    0x50409051f0f06020303190b0307150905010c150902040f0f0615050a081b09040e0f0609120f030414060103050a0b070f0906050901020a060e0a0512040b03011e0b0703030c 75
    0x1920643e19079800652868031014000c2c000e00349000c0c04044800d80b103001c100030a4409000000041c10400303c03501c584801c03484003400d8403441d608458100320a1034012004034030f00a52a0f03900d03158002001801d2100c07400840d0240020070b140c221001d05003c00c18105c41d1141e070050040762010000000c003900c0c5070344200e8062203202400c5001600040100d440169040c1807040c1e10302c5400d403407601e4110500040b9058a4080e20f982c103080c0c0102c02c49482d07540e800e000d1280c0c4502c48a000d490f10195151100601d0f000b13001301c400310030201100080400c0300c0c000c1250942c11500040f561070f580d4a1030219070701e0001d04001c07591207900340f0218000f94080d4452032044405ea40700c02c0301c0d241c02c12138116517503001041254114490040fc50011a400b8405c001171200c500d0007608000c0c8181c18242c0c40e01240b43c1454405260801081111441210a49055510503960114000522074011240340c030300c1d40007000314010000b0003108068259102100100c3e10740c54022400100f183d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 141469406 1250 141468156 141468179
    0xf070f06030e07060e060d0603050a06050114150a11100e01090302120f070303020f1306110705180c030603071e0f05090618090304030b100e0c0307020715050409051f 73
    0x3c02d40300451418441c000c00b926203600545014031f109107001403050b541f61152441c06c08031080980d8641d940c1d1006014800e544040e94942c4071080d11800350341070104106070002d2081c1600d40080041c20803100003012400c1c07040d0603225155072420f101e101300b1500024020301c03450a0403005407080780003000d55034040c0800c1e907655240203907100e1f08001150f07c1c194082d6201c0e101d5030302c0410041091400e03084c2504490b030058625a540c411100d45004001c0340382c00b00303075041244511202c0c42409030008080c040e4540c007081444015450b40c0300c2501007898555180c206030514100801034a8044e011607440204445400d4003031070f1301d00e1342d0301d00740102070106440143d081444030b0082111040c005400f00e4100490408403131030a540c0b83c40d107036805c2006851566040580300410842c1158180078580c02001e050042841e6040c4028041e40c1d075900703881030b040044040946840882d0140c0300350b60080180b00c8082c4001e14042e0002403c12020000341401d540070080e012401c0717803040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 141470656 1250 141469406 141469409
    0x61c0c020a050c0114041d04020a140f19050603010b120109060b0d09021507060902030d0f09030f0203070b160510060602030403080c0106120f200d140f070f06030e07 73
    0x240c05800c0301c07805480111750041c420066545200300130400042c0700c403818180340001d407a80c6541602641418410000b030010030342e20203488503076218075255440e640c00200c80c50361034007250700f46c1006a0003900e20800040c40c7c0d102a91042e0080000141c4a03014002086248071101d00c58020340c2e00c8280100460307440380104041501c00344280300e1030001a9100400032400148003400040310003643c0c222550048000700c400c41d07100c3c04108114201046a02030000e80307820144200c600d2404001c02c0c07055144406080b20625420078019501c0c00c0c4803100c050407081c1007090340c0e0a12680e52000246840d41e00311740c10b03c902c24100705080040d02c41c1d40255101d0343d003d5803801d4510344490409030015003402803155610800002c4a0320b5520f40d02104030310540264005e04200d05110a581402e81c000344000b1810414034119903440900e07540c289548990806107007841007008600d840c2e4602080c2a40b445003a5000c903502c40c041c8450000c4030000c2d03400340700a00600240c2901c0700c009 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 141471906 1250 141470656 141470663
    0xd080a0b1008070e040b03100b13020903060c1602031005151915030b030706020c1302030408033105071e1206090f050a080d0b0d050c120a02061c0c020a 67
    0x4100108040511407103404c000140000c10100e225541400001e00344002d0110b0340d482243e981d5070911590501c6050000120b04000302107042140110201b600c0b82d40091002c0400080000e09045090880e403c4591054010341100c1000c095107000d60018542918110250ba050300c00d100f1091a12411001c0307840d060018242c00076182a011030140d5840020030700503da10303001079840c1507e0400c0000020241d5a0081113480040c8050140a010407040804101c1c0100704000c045450300080700d40000d02407071100b020503101101594a050b9098141c00f03c0724840d41244140080055140251030920050500712211580c40e028130a0540c801c0859209441c40c5140c0800c9040e400000d42c0da010303076809640940139541ea90b042c44000c0713000300c508034004551444001c1c0c40d40314486001c241556007402283d90b54846680d11001002198440d403413500206400220900c20801a9076000e017205889412a20440807400b2035000301541052034141c10800c003a10000c0c5529401380c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 141473156 1250 141471906 141471917
    0x6080d0f030c0c060515010305011d0c030a020c0a05060901050901022703160801050703110711150906040315050601030c05040e0702070e041b09060506040b09120d080a0b10 76
    0x440001034000c0c05a681000c414000800100804240720303015030340c886d40001020a0245000720000340480320181c12810001038204089a00325841e02c100c00e8000c42d015110684a503520404070010744100010018140074448102080200005100c0e00405090000740403a03500c02c0a441d08034010411201d0076a500c0705600c000c11a07038800c44d400c00c014007034252000c021064551703a89003903944e84040c04c560355500c204140d0661604c600d42100040b1103502d450160700d900c4600d40e50359400015445070001600100010048200b150320b4404082c140c1511556241084070010304824007031030b01c1500b071400042196220388205c00d2800b4941d06d61b9402c0a007021000129080010040d406601c0340550100d81d90440d400c100380300d2842030143c2d411817a00c84a010300c8455155001422850401006011540d2030505650030b441c02441c0094550200c400043d0241e80411038112044c024129868200e5500108003842a5000d0710207010f0320314072805000e034401100d03500800040 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 141474406 1250 141473156 141473177
    0x12080a1b030b030a0614010609050a031a070309120c03030f060b030f04030c020301060f030210140d0c02030f12010521030f070201031b2003040f03060504080d110d06080d 75
    0x6020b5031208075601c4015080310044070141c0d80e44000c840003020083c000e81c03040c0c00104451584524001e01034101034403a448000d04e5940e850a00302c06010f212a0301062410000742040d2003540711011941c2c101724079400060a1039030203840203080460550000b0304121030501c03c015613000d402c00712880342c90b409246981d100c182070b50352403000d403044042000079100349025907400d0261201406000003000450780c07540c070401001c1c0d2036943c0317500d00303018891030039600380c0000c402901d840b0750390710101041003140b21500b241135120b12a17990300109804076080c2101850844840d041c0c0300261540404440034213000b403108440c2800304041a0f00401403400800021409001e03903134818103000ca12042920100c0001c141040390781c00001e50b8640c0c400d031600282045042144002c54060f6160504140c4008468030351800090603942d1183d012504108000302101c0c0c0364150b0708810802402103500428441e884810b04058a500b04403020602041c003003260380700015140c803095401c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 141475656 1250 141474406 141474461
    0x109120b0f0601051c05010510030b09010e06030f0f030901030e06040b0105010c0f1a06090105040e211b0102070203161404110c0f03070c0e0720030708040312080a 72
    0x80d074000742443d0402c2024010800c1c1707100d001030b50282a0f0544140800c0c158140700901041400c1c02401404250030300f00001440d86400e0106419100c0d4090a00302560718000440c2c50180003103450a0180714007803900101c42d10210251145850036601400744124000c0c801d42e5550082d50302600c0032003200010440d81d03008801c007440031417080c4044d03508805640c40e0030140601e1345001c0e6410502010400915292400201d40902021501041031384c41d00e40d0f109594440f040501e0a059008203140b08070a5403820030f071a1f005400d81075040d030340385940b1800c5001c4c0d00509d10482c040d210300b034039108101a00e00c41640a4440c09211308812614001c01c00c400381035070609000c0090010024105017400500c600c8120f02810b000a583c0c50388689040301c03260105601000040c400c040a000046034040380004210b407980010350460012800f036242584503a03503000b0800d84002030000100a4401d010b1401001d568952500700e80d28060382c07806856046c4000c074414031102e69015891b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 141476906 1250 141475656 141475681
    0x50f2a0901090e01030f1b14040e010f111c0501050f04020702010c080a0e031203090a08250b010801151514090901080106030b18071406071703060109120b 68
    0x108038149400d4090541d540042480c540c402e800035522000c2040f02801840400001500c100000e09a0188040c1c900074041810303101d081c06c034600c80d54540703148404030082500302404a0210010400c200704400b02641e8440e88005030b410400c0142d00c80401145041d4030400d41219000703820a1400da0303c0504110007035021b00401c9041c4420201c0400c04200924042c00c000c00b80780c1c0300c5061001d241420140f502c0403c000b4035000d00000c1003080a441c43c003060707140c05c05600c1421140c85408806204c1030703150540c1c3e05000402500c0032410b043c0030780760000e00c1c102c03808038000f048446524094114010407078000d40c0d510107026120741006d144100c1ca02c1c0444810406071134202607000740004c410041c01e030301009040c0e4488c0c4050080c040d1540e1015007106020766143c40080d04800c0f00c41d210f4456214007141c2d051100c00509094440f101102c0c0902d6102d00c04032404401500e6003030150b0030030340b080b038000b548807680481c000100c0041e120a082d005070172050a559040d100148 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 141478156 1250 141476906 141476917
    0x2010c0b0703150b030601030f1118120607050d0e0d0f120b0d060b36040305040306050901150501020d02070e1f03031d010e0d030c030e03030a03050f2a 67
    0x4255031003081c04403140025510f0005052514072965903414440001030644803800280680d442c07400b4a109800c81000084a61121944e4407c00c1d591004100050290005580d00d100310f00450003000611644840145205504040104100c11440c10b241d603071858091041030104400700001403986010b2071001e04521044a004a0402d040801060703099004803001c441903030710f44049890b5403030a490f86d00345001404007400400c02422034140020080040301100d50301c164000314090510500445e005190440303c24095800c00c013407100d00811500240459503060030901240d83c1d0300c0070800300c48100d099030047c0030540c108417150072a250042c00144d44440038071202080e00d0100b9030780500460080e16404140b0b012903100d220524000c200003810132050301441142a500c00740700796840c64140c0341004074074406141c10380d040088201c00d070340c0c10f1002180141c031540d03060304200d00c1016002c4064120391900400c0c0e543c0c140e8001c3c524140800d484600b2192060035002410 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 141479406 1250 141478156 141478171
    0x3030f020f2a0703140d0806090414010b100e150f070201030203130b07020708100c052506020415030e010e03091e0d06060501180302090604020a050c0f0c01180302010c0b 75
    0x741d402d00348a007082c5446404e070300403070f100c8035042d811448140050111015180640c14031000d103141940004111040c0100f006190b401f4440b00c8a42500b4250300030305441e03001410351115022501c0000c0c290310646840c49110340141d0f904500702c07003084400c2c0c5171800580f00c0c0740b50400189500560207074000414802da8400c11800843c0801c0024480501070700c06070300070703080c00b90600010b0b5091400b10b451544040382010038000b020390740f00c2c04803801a20b802c0004040e81002c10301b508002d50080001400090020901040301458103000225007201a102003014000e008091401d96441c48203070403481d041400244282e0500b62443c240c000c906110001d81031082c8000078100000115007a6800303030b41c69506000030350300040d1780340341068a520100c15951841c0c1c005501c4010007041603009540204041142e40d020307005403922040b417001641da1008c01e03c040319039135500300c410690010f001881c0c6800b82443c407010b22019290180c1d00c10031181034a40750032030b200344080c2011 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 141480656 1250 141479406 141479467
    0x50102270f0f210a0215030f01060207060207030213021e090103060e0f13050a0f0c05090108030306090a0b0111070306020712080c040603020912060a060614181212040e010303030f020f 81
    0x1c0c0166140d00c41283c012122858064480c01c0074103000151008c141c100009651103450180b0503c1e400054220441e54119400c020710303080c01580d000640544a00703406504140c640c3c81d00500c100e0310223000664020391b004c20000e640d03091103082c02c00342540d240110300198070102d8214880307000c060b80384a00544c201d49040705190380d0044039941c0100c055445a500d010709009501d440d0384001d00501c07124006508605014000400c03000000e4109612607694607070081d02c1740d000d158500c0300000000c050702d03a440c0d1341c5d0800c0d001035480103400311800c00d816820000300d0b0340a80c61441c0214100c2c0030ba103042c07905085041d4020342c018a0446d81c000c05540c0ea48000c0300042003014412040b8641c040303a000d1900c203014000f0b40140300d401c0c0c9940710a0000701d03010002611402c0b1145001c9601110090090310603d0a00c0000d0950080b01c1d03200042c08a00c81501d02c00351812648250350801c00303c0d11a10001040b8051301301010480d00c0e003000552030000d6a2540380548684c41c950a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 141481906 1250 141480656 141480673
    0x160b041211101106010501081509090111040806040b07020303010303020a140a0803090f0c01112e020316020c0402120601030b0103110d200306030a0f050102270f0f21 73
    0x4600a444076120000200340d00801c3c0000314040c8411070041c50b083c00c104859040c1022184c0b660340c14901e07458042c0c00781200007000c2c0c1509410050011082e5200706580b00c0d00c4003039454803407404517003c3e84c1c0003c920001c200740501c0082120b04980d01a400741a6600d2244d0340d8040e0445c1900c0303410198401c085030381011404400003140511200f000074200e800b81000c0c8541002044071030241440f6170401c0103010b544d40400c40000080b412000f01c1320030282d1406503c2d140c018000516101c610110802c40114080010800c900309960225135204201c103080105030311502001640206181020500c254000d400001e2941014140415645400217120840b81c10550240e119140c8501342d140002d081e59401440700810400004d141d45440c4011035030f55550b900d0020081c0c070701c00382030381c051050030340c117544104081c02408d541800301a604840d0381108034042c1407092010411034400b6192001000703160300c0c1e003d45440381c8425250000c20fa00d1460119900c1140104200b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 141483156 1250 141481906 141481909
    0x18030409050a0b0306090109080d021e070f02011b0804170c030109030302130902030c030705030c120f07080c1806030901140a02070614150607031704030f02160b041211 74
    0x541c510444030076800081c090b80035020103180100141000d41c3e03d901d84600840401c0321641214110459404003507500c030388103c0103000202005020240005001c10000b04014140100d020010f000340d8541400440d40300c00700090b844000001482440c040000300403c0785800d03400c004904841043d500a0612540420300f9038003d488201d00007640001c0f1203800d0040e0b04480070207402c08600860452030b26510001151002600748003d0250100c0042d91500c981012240c0070321140fa5180703076506045c0c6c0700c0102c601040d100724012030034600020341440c9141701a03400c0040748105603910a04040306002040c3d0028045115035501e950300b502080d800007240d40d0049000802c0180e0751805820b200040307454880ca0645200c208038288042c0040b6034401c0c2d000d50008540656881c0c03442e00c2c00360349411303c81c46085000da40c11001c00040c117802000100400100e5002d550012204000807022401c0074041d4081c9841c00340414051403000e0400403508610074040344041001010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 141484406 1250 141483156 141483161
    0x60708061f080a050a0902010c080711150405010801050f011e020c0612160f020a0303050a021c0b1503010515070203122a010606050f03091606021e0a02060318030409 73
    0x5154034041034400c03043c400c824101d031103441c5d03000212001c20842d80c541e503400240f003211078003805072102c03002144200600c01401d03a451003040004002ea40c4c00d9101e0620380d0345541003403040b40c3c0420781d8403000245905000b048040c040c40160340e60142002c5101c1041d12600700f00d02c10004600c00d085c0003401075180c1c20020320f01c40500c86e014443c07900d09a54242d551088a81c0103208009581c2950514035800180c44c07001070303500d400e0100d600c0c6e4400413542d00074010380c40310b0024406c4001d944000314000c0da10128181d507081d5040c6940b82c21403000c00c0801c0c8001e106060308080d0603103801c01c600e1007440c05880000d2005060b0380b424420004080f203030b500000194580503040042641c01114158040c003e50a1130100901c82c0d10326001d006011801500c90a08207128004000f0300090030507c1101003064030504000920703903c6040c000d5451101c0440780c0f12011000c66100c016400014800d41d03011360080902d403442c0d84d504016080003c81c1e90f11448540700c03d0102140541c0c035070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 141485656 1250 141484406 141484459
    0x91e05060309210405030607050c0124030b1e0601050703020a0204020c0607090f150509030114070534030309050304080118120302031308090112060b090906030601060206070806 78
    0x150050000e0341064000824650f07482c2c1810840210410040007103803400b203940c9900074110306003103840742e210401d4140503128800c0407022540c003401081301c2540744a20303170a0a523401505034103c16a5503200c8104410540e1925440032a039650000d811507100c0d00050005034800d105442110303615034041416070300800054a01c5030001e00420076491303401a008030040070042d5130044018a000c036210b028400c212084820404001612035081c0c800b50030140200043c5a84e030710306443c0110000300150801100d20031b1710b000c41c0381407000c101641c0416110700200e002c820900704c00726036019402407201c1d03901250342c2c0c0411300000501c804207102d0011003680d801ea1810045625280c044a010b10188110703092510520511500b00c5950750882c10031a8000c00c407135a40c200d5100140c0c1c03082104c11080050600348200800c1c40010f010280960941c140e41020560b02c500c07042603201e080034003a002c0143d000c0000561520300c2148d00640008015102001126880700340c84d4021164 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 141486906 1250 141485656 141485671
    0x12d05060306180411040507050726160302010606090b09010e0415030f060204080606180f060111010606110c0111060a0504060b09011413060f03020613080304081507050a091e050603 80
    0x1045c030401840c00e050042e0356010702e1070f190031440c10344507698440d180d03160780c840000c1500780032801111004185040700ca80b00740f0140d0044e00002d091400901a200714018440054080740000a102e4442c01c03d48508500503103440840300c224000b80300050140302045140842546400001300d01d000e01a203804a0255101681d1941445109072030120007a181d14010004040800d00c10060350851607040041d003951107080e80c68880040310140c0843c4d0582d03000707504e402e07070026425421202c0900b114071aa410360745003581d5400152000f500d144000310064100b080041c0501d460390b4801c46d84940300c1c03600001d034107860344041442400c0036001012040761540da0310340c0514290401c88140c00d1040030034040c1d641850000c94490a80d440001d009060100300b90340000d04c520003403c00780c02020700312a152903640841a581d1104200314611811090000c1008a48207800300e40c8075030100c0d00e520b040c89280c50070301414401e55030820001d0a031800f0010515554550042d400f0b00c00713 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 141488156 1250 141486906 141486923
    0xa1a160c0801150f0306020a02151509060904050606010507030504120804031a06130905070503010e0307031d0a050f04091703090c06072a0b040e012d050603061804 72
    0x3070000540c00c403000081d800d403900d141050708002220381102400c084c1ea41c400e50161715250000001d038074041c1d49200406545500c0410003500750301c20f001c00400c40c04211005200c035140c00301800340544043c0c5020b4850703002140002c4031540500e00510800c1e2092401e1031a003961103c0d44050215040b404840040000800f00700b4040d031109540f4507070140384201c003818100070000890408205c0e4994440c15142c2c2800342c18400140100001040f002d4000d00c0a48250070585460340e000b040100d01050346500d40e102401c2540c1200c204643c8090081ba50260a103010400024078109959500a8a9044020010301c002c4100764410452039182d64590400c80710242c14100d0108000c0c0c01007100303101040110303101704184040c0034444883c59184865060a40314035280b950841380d10301c01d0009000a44500b500180c90403207000d680c0c0000807103500100d1a00c03400070050b01d01c00c440f40d40f01003400a85480c030300458001000030128602004104400080c1c840c044a0a481084 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 141489406 1250 141488156 141488159
    0x60201050f0106051204060f0609110301060f0504080601050904062310060507050606060306030703140307061d1e030c101b0c021c0f06090f1109060a1a160c 69
    0x49503039041d030380501403e080550400780c2d1088101501a00141301503d81621217038000141c018035840310025103429201070001101c10460381041e580280320756400281b002c1c00090101744147c1c2a40d065840382d1002e440c00e0307440d0808002d8420000340065a10031359441944000d00d4025228510a0290ba40000014586080349a0b03518501ea4840803c1c80000c000c0342000074400300304940e00200440f01d0790340344d840b03060100e4944000da810007030092900030707031414182c20000060240b203032090034280f0441015a240128110788030ba01038002d40e005400c8103c2c0c0c440300c03508100048030b402c0304690510b040e241440d4580320038419580001c0346c1d52103403a40c3c41e007903110b981d0500081e2420200c00d08040e580c0070512000c0c0d56040300094020b14020343e002c00c25140c1c29141c845030800010300c084400d908000514134094003003124508045054220f841c24a032940c00e202d420005d220500040c5090200c010707800660010001e001010800712014064044084c081c582c000c0350b540341c0d001d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 141490656 1250 141489406 141489421
    0x60303030b090105012f07080708061504140601031a040606050a1d01050f220303030b090603071536030c090603050307060c120f0e3304030c080406020105 68
    0xa0006070042e9040000b101c6d002030fa204010406400d44100403504403c6410043c00d61908007030301504403a00a0103940c400050b5540d0015401d80200010402150660030400410007120408501e105442c911240000c141d51b001c1d500064905401481c0725460f80c01a00004040b5a00c43c0c0040021981c08280e0f5010a503005039803604d9a09240d140c8041c1c21003210000e4010f00071140100041c0100184042603400d40c0f21041003030044003840d100b01941c481c46d007c1e0250446a6400b40181c25400c00522140703400550341048074440c1e89011011000010100c030950300841c40030004c4441c5207a550011100d480c003070b0b00440142c095205130b40b4290325000c0c0c0344144c3e03644101050381c24036034188080b810100854500d26031010001034044141d4506561030b6121004a40030945070452a03641e13004a6048010084120800e0350a10542c600c40d140200041006e000b8031950300002d207113451107202c3c10701e0390058000d0030100b88003005a80c0b9600aa4000c5e0440300040c0d4680c0c044c003440 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 141491906 1250 141490656 141490669
    0x7080a030804060b010e040f1d010506090c0a050c070f1d0f0a0506121005060a1d01050108042d0210050a0c0b04050102040b0307031a0a030f0b1f09020405150702060a0f02010f060303030b 82
    0x264100400a00050a280c0300107418a1006040b0608ec507400092840c50a8016002c403184000c083d802d4803040395880444900076401d510401d10349440000c1c00c00a001600520207100d04520481040140c9031006c2d41c0c001088010500b94211601c00d20500d940b10b8200032825034062091404200c0e45000310038054428901c0d070120219102d8007070b114102002010405054070800c0c6040d1840c0d648500380460f8001c4494000c1d047c10032a42d4815a810708114041c0740401d00a0320f03503c1c80001c2c107003c200c0b803600c01e0300c003d8800920350f4080440060203186040d500b0a008a0001d800c0a888103104200760f801035541001103039a420010390810001e645040d441481207584811036481d40d1200458401074103402040c041580000880c2c0303c2c040060f0029416210703168544860719481c6080c000d40c0036014072403190020700c0500b03401007505801c0b581d10a501510147c1000c060100c10344599140100c0002555261120f050078005184a40d0340150b00a07030700490b28000d03031001d0000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 141493156 1250 141491906 141491951
    0xa0608030c06070c0c030611090301050c162402041e0902040b030a020a020f0f030406110703020d0b07022a010e09040c14030703080a02070807080a030804060b010e040f 74
    0x1040d800c184110080d685001c01c03110f034081440d0605062070706203464a880601c000e5040200703214a01919071543c02880d0015084c018029002008540c5829403000d020380140400e0080c000000b02c5004006041c682e800d4030000d402070000d03e1036243d21804001642c1140d084494526022000c15a818410003200001030240d00c604502c1c09003490300040580c0310080000d0006030700018203070301c924400c10003400221340c40d0065030001c02d010500d06840c1d501500c10403000444d160083c0e00750b03200104180f422130703074001c1200080c00303480e564040000c80c00411010550140600d10002645030116003042c0c1104446000e810091010003d049500c215050380d00404200b020000028010551001580c2402d0305510700c070500c840009140040d00d40000b0604100480c0c00068503070001268410384601006a99100b0780b50005550764280c11100600081c40f01004100851040c2d80300701000300b4185000c1d1003074107051000c20241c90100441558459030b602e000c00e0030900624a004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 141494406 1250 141493156 141493169
    0xf04060819020906040b3a0c030e0d031e050406060303030f05100509150d08071106070c0605030c22030b0a0902030c06280c110909030313020f04140a06 67
    0x14240f80c9000b0120700300e801240203004002c100040c0851100070440d00c200783d462000315440240386081c90207400d1400112042d01d0125007040b800b00c020502070f0060142e00600301c3d0080000e050480002c0700908900e820103400c1c032036040fa0005ca05180341c06101d101d00e00903400459994507501e0002c00f191540e0800d00606803030207050100c0040c000842d0070460340c040f150580c00da140d824401c40200d041c2a0f800d64840143e81c0b070706007004201005044e01134040c203030103024869514103020442c8640c05c0018100c841100041c44514003810207550044c0d40c114201e800c0025000084206c000e2100d8401d02554254004100704022044e0b140c0d8491428102481030124950200341d481d1071030203510748039100100d03100000902d004d620880b9060103007600040f440d50003801400402514805032400600c079031240d00745050a001d15401600e4000c021403440c2c1c2e41003102e41c0c2848840c01d08030303844131000c078038207003030f80d43e0703806003188046c0b43c0100e9110306d05000b51a00100d50460b0b0005 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 141495656 1250 141494406 141494411
    0xc0302060c090f010f0302040506070f0c0f18020c010b120115090c090b180d140d050a0905010c050a0516050405220b15030102040b03040614061507080f04060819 71
    0x200c40544500030201400f583c20300b001030003411180c1007a0080d020b5900400d0300010003083c107805110010106412190240d02b09403160382c0c0b61b000080448410303000340e000d080f003184a29142104103600a1501e249800d00000d680030100c8001851402505500841607441c0d08598500d000c0b2921000020200709004128910035000c01429000c001d210700c103103012010585d11841007095044048550000300591880b01c81c1d490550b0b002220703080c0c00500d44c8203403410841101c2c000c0088a480b058980c40e150940f5140100444201c040a8022100c0d4080c00310350b44006a02081680d41030103400c1c8044080d68140414841210001030024240744240c0600034600c121203005c00c001a90002084107180e610404e00112001030130114030b03099840003500281c0540841c000e98015885035a0501264000c1d062034501400192105940a07803c011400950900700c0300405403a407040207920f00f131409174040d003a03030740d013143c0d001030301040040041046030810809202604005c0003400c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 141496906 1250 141495656 141495667
    0x40203190506012d06020f0f03030c07150906090303020d0c090e0121080d0501030204110304150c1704050705090112030e010c02210d031a01050708090d0b070c0302060c 74
    0x50302da880006114074a044030300154945103003840380000040501c400b02901032201e40c1d80c80000d40d00d40200d90f1180c0e40740903440006420881c04001c81e8040c41d450002941402e84035180d4154562810211080c080e50703400d160400107261f40030307885880703010b62001038075045181003580c143e910181d00c1c2c40404c040440e01f4042c2200300408036055403030b81104d0441402814910b04004028440082c00f00360002c0f461505c1d4000541100d41640c3c402d0301d0502184404800c00c8116010545009189080060f070740b850580311640001566022850710f99021703140c0140002c40c48a098034140ea040e0003075007043c40b00b420516080f5005084200c100c0c0f00c40007040e10020201100e4050080c10000b1080c1d950042d07503128005211301c4145400da45030074012420680b550b50803010b80506c0400d050060301180c2c100300d00031004440c0c00c180c40351858040f25945d034500e01c1d84901200ca42c440e8603402d2174000b04250400e240d00ca60901e40f03421690201908000e441e02c90001c2c5690703070f07800c0208003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 141498156 1250 141496906 141496913
    0x120f0513201302070203190b010819211209050a0501050603030307021c05040510030e010516050a0c0c09060b07060b0307050d030f0c2f030715110c06030c0304020319 73
    0x94a0180c0c0280b000042c1c440032644002810100042851160302c1e80301041041032101608000e8100c5141c00c04aa07200303406140c591210402d8054060403140c424003040e22413215085200038050081c1c505040036908860b541c0044070070050041e6020303448444280100301091140680080d41140158150310700810000d665034a9400f45c074207000740c544424050741d030040c000e4802820300241f940c20f0002007070300c0c0100149030200340070301030b50300308804221013208a10b008001c4c03c98595886140c201500416507800342d8003141114845d105a000003405086881400b001c0c15030454050f036a61000d080450540d03001c44041071180e000104100481d41c0c5000c40c2c03900051785800e00141521401e88140d660281410015040c980019007500100c40322824185079000c000c00c1c03040389240048141995054140189006000d00c1ca5800b1840c600502c00e0410302d102000031109031013042c81c003061140e041503a0440030580d000c0180030031850240081d060320407810850181948250320f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 141499406 1250 141498156 141498169
    0x709050604020f03161115090c0a0e2a180a0605031302040f0219020d11010e06012d03050601061101020a0f030e030c07030f05150108030406120f051320 67
    0x401d18020450010603600c12540038034283c4041c28070700790547d80160118818981225022124659203001da6075480759140390099240042d5910500340d42c03250780c1d450100000040c00d5454010300c11604240c103004114405009280b80c4a0b0300d090b44058121030024446c1c080c1d2030b0740002d402e2000130320070402c03901608807072185850b4040300c010640e00d00068200300248034414840307420841c4011020100b5800003140032903004280d81d902c041c11007121a060884040844100042e0000c0c00100001c030307592420200092262507089150a040e00440a004660303a48100c440b500488010402c1a41040c042d54400c00000c1c000c1d4946000b40d480201802c2d9141c607808140b50761500041d03d128800c2050700d480d0f9441c10201c4541a0300c1c0c0c18940400501c900040342c480c4a01c01c14205052844c83d41036041b50131000055080c941848415600844502a9000025034400042c00c07054810300506002e001d44c0cac2c60005c460362403824503041c4e10340f6038007002c80f00c0140052480202d4484070b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 141500656 1250 141499406 141499411
    0x1812080c0601080a1e060f0e0715031e0c1407030305010618080d1d1305180a021e0103110a0e0f040c091a0c030417010f0902151b07080709050604020f03 67
    0x2d064040e080e240d507190140040c041c201003187c00c4e40c600300b8214446400011488203544039220000800701c03c070031049064861403110502101030100c81450440200d800c210f41c0c851032400c228064001030a1480d419802c0005d00f80d0000e0707126001005017540001502c125080e60703100e42030b001c074100381e00c80e5030300c0091840f0002080300110b80741c180982c081c40100140d0b40010000701c4954905803d00c0c019003015943c0c403990b000d03a40108155041d00041e2042041c0d801b4100d1501106404a020300201c42ca01000c0c0c14162143c41801e80004440300515442138030f0307120107020400303040500500c898446201400f039071611410300344854000c80604111a0246490304000303100c04416800c900440c0340b101c0c168403011901140040903180380d8040060548020048003040905510a0b60240f503c02781d00706018400c400c1e18101303020020181506c103406c000843d071600d150342515105203a0301030403c54111410905c99001240586a04404212002d608154164484c2c40085c13001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 141501906 1250 141500656 141500693
    0x3030c0f0d0f0204090b0406050d02031c020c0a0e040b06040603170f040506070c061103030403090501030c051207020c030d14090103092603061c030e011812080c0601080a 75
    0x200707081c1c80020071a000710a400681200542d15280d0710b04050001d0b010107040b29100e2401c241c008201d90a080c000110070307540040050019070110100004011650000213045014451942c40252140b0100704c0c020410807451041b186401d042621a1a8020f00041d1145042c0101000032440c6543c03103031800c0c00c041601550b540011800c02613288129801190451808035415042c09210340056089610781d485081c10384d15800d1000c1d0312444100c0d002404540300a405110030752003644009080c80d058107000b41340c640981d1324038489450848494006a020700e60840d4a41418406160110524204000028086107030070205001d244172031810556113191407410301810710004641d1081064080c44091030504020381c1c60780c001c8650341d00800c1a2500c041d803052103800307040c3c55203030145c5c1c500c40d0308115800112260b91040420105102500b00041444030030300300640d0401c0c0c40341e03200e0380e0345250710750700142407040503440b403402a005400075802165001402108c0e0080 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 141503156 1250 141501906 141501937
    0x402040b03030706060b04171204060c021809010c030e01090b13020d0b0a0501050f0604080c1905120a020328060c140c010c0e030d0509060f120c070c0803030c 70
    0x10100407078990f0296400240496040c8540081c1c203280c548014800c0d600c2c007404510248415100c000c1d61081c10b007821a2100c10200300411109108103d41c2ca8940e100401a0201c507503072804c40e0003030b0b05c2d0a45484a00381d568480441040c1c1e00352050003040c201100090007000030035103510800820040c03480a070343c083c0154941c1103542e0082d09a5040390f2201c03151000d41401d070750110080c5001d000e02c501880e51010102d19524100090701c00311002d0034018030f1107643e01c0040c0b24444044200a04d403801d0150783c08900c41e03940842d15200a40c0d65402001482228010149001806211004000c9800051445039100c4441a072821900458046501100010102c4000c01303401c03c070b46000c03c0f0114045003000010b40000025498980d40c00140010280800da00c0c0c6000000150200702c01f00405a80b40c200400986500c214200c2850300701903500f032000c840e03500304969080c500280000c100c0208010b0018503405041481c00642c19407a04a103171126610881c40070781d00e00c41 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 141504406 1250 141503156 141503171
    0x2205060301090501140906090115090207030c050f0a150507080103030c0302100617060901050601081302010903020301020a0e100804030804110f030703062f0906130909050319080f040204 82
    0x8809401c08410b85511078001c10182d21003031214400c14005881030170715401000302082001005000d00d01c1c82055a54000394010314104140c1d000750b2010303108800b884960740203d808600f050080f01e000c0c0207040c01a03e4000305034a4911040380451041031001498902844641c50f40540003505595060914071b03505521418113030b1401c0403400001c10060b0820101149510451424018070072a40d011103110f0b850314686c040c00d855080340c510340020312600009003a02522080b5a034075500604007810015100c2d00400c0c2603078410000c000104001003006411030601602a0003141624645a10f8604150394020300000020303002800030781000c03441c801207588800d00c0000780c69004040391b04403075403441d24001826001d043c0040d180c042c0c0d6140141220110811050703038400740c0c141c61030141041d0800006420042d400b400c040ca00c1c840100e1914120b209c2d1a80c040c0c0103100440e100c0346205030140c00d488102010004108400702070046045500010b43d0b08158111004500613 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 141505656 1250 141504406 141504409
    0xa050f07051c030b0105190e0a0f0803070309150f080a18050c010e151605010608030a05070506011203120e190308150102152806170c220506 62
    0x601841034080c00c0c1e4001c400d2502030074605600c5140300700b90b00341c8061201085003001511a070080c003c0d10800b0000b00c1518040701489510b0b400b20f0004001c140001c6203440e0b82007804480c802e6041441d0300c2c0c0c0005000d00500d50445e45240c018040c0007542c40a0b00030316040105080741c007a0155080c0010034000c0740002045070030240c107554a401104d03c40f07410034108555100030307022181d400300e1754191120a10f401d2620b100c0d06c26900011005141c404040701906205406680c10341c1d0f00d5599000c0481d04000500080511844030b5407543d841d21050304001c2d0410006030b10011015060300440d000294000c046c10f400010700308000101071812041240c14904080811510013204041c15001c0503000500325008103144400d110114020303000590341c1b1886c002699118001740e42c00909280c01714110140c0b10011088803a0b10320704200704100969080744c105001200c4400981d08805908201c604003e41d011901c01d410072410708062a80f078801c2c1c14414000b00d0300e420009541d0b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 141506906 1250 141505656 141505687
    0x50405042607062f030105030c0f030f0111131d0103060e0106030503030a02040315061d0403030b03030d050403020105100510030f09020a0305010603120302030c12060d02030a111003110a05 83
    0x41500080240045500900904404512401403c00d002030300032000d04d0b4400c0c03031030541c1d0584030007800a00c50030142000700070750004010400382d494402c03004084200f01c02030042d14195a1002c1d24642c80d03141091030401c803004031b40c020303440710384030100482081407110341403034112600a08000740c2d4540401d00d00d400340c0310740d030006481c40c8000014003001c10070356401441180d0089400e540c00380e55800900d4143c401910902549003100500008030000c1c0782d44103500207209040c00102984064003003402e54000124071054a45d85030100801c2c942c082c0100f0360f0001c000911001c0c8181080d000030a11a035590300d640402d55a94482000780b11998002c01080b5001881034080a0b640e2400318043c2c0402d001c100c0c5e20385042d00c160501c15001e40203503401040704901480c02c0c00c90301d0742c001c40f071101c0090125074043d04111840015840034000d041e807007802510b8185d050550740042c408003e100300605401c1500d054105d0085a58510a5912800b10740ca00159035115074041100c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 141508156 1250 141506906 141506917
    0xb0103110d230f03070b040201030221040609030e010e0a0b130b070c0518011212140d150b09091501030902030d0c0c0501030b0d12050f040806040203070504050426 72
    0x1040d4901c0320700108524641100e402d440b0080d03040b942c036070160070100f42d00ca001e000d0740100011212808240150300940240030b1b403200800030400112038064174042a0b01c001c0e101501c0380e685d15046031060580c07189880082c00e00a0804102c100d042e10f0100d101b111540c490090800c1c00403690b2821400c000007480010300c8440009525040c481c100050510114031034280302e003040350007040140c4030707406200e412540c0c5401c00b00c9034040d007600c6410704001018091804c020001c1010784c802004003000c0c0c000d0b006e0b02c4100045080184101410701016500964070303032881400390500e03580c0d41024180e8030003000d03181c54240c5500c00b401a0090705520030000c0d818007031900c00c2480e1a174000f02c0700100c503000341c031004195940c400041d030407503403020200703600500f01c0b41280c80030403200e401d039800151181c6007007403514404145605142d0442e401001158101e881400190f207010425013000d0401140d0030403840c10596600301c440011990146203207407050045980c6a032445050341c2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 141509406 1250 141508156 141508163
    0x61b02030102041203110105160f050708090a09020304020310050c07020d05191416050d03030c0215100305070b0a092d0902030601030f0c090b13150504210b0103110d 73
    0xd00c0da0391454041c0c0600001c50030b046c502d40c41d040c000380059500540c5240e40c0303200da844000f01d115814100302d03a90340c07100b0410755190030100130000080d05e07600300c110010b0500c0c1d2401600c1e403c00e8410141803c01c1c98101020840c18a000c0c42090041c1d4001c17540b010b07504480443c00b000003031070010b04044060007540d561000c04501032052103503520440590407070135805c0e981300703040303042d0410044002d0b4021507802030080c2c04030000181c0a0780c40402e41040500454001c0845115082410a012281040107500124003001000801c0248101500c0c0424043e828160162030050200000d0303c140c0c40b207003150f00f42c540c001001d05d00310303403014003400300505c4020394456002078040d41c816aa160f002a160000711075032610948a9401e01d006543e6415082a2900c030101c0c031640c11a0268080c0c0755820840080d0508014040301140359498a903580c903186001d80503c545500c80840c102179080a062400000d050741e02c1c5207055aa0101d14480341150420100d40400f08409008 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 141510656 1250 141509406 141509429
    0x203070605030709061103090405091e330c0f070b130210080f07030b0f040f0906050601091d18010c020a051e030d020d380a061b0203010204 62
    0x4919540d100c07008620460140d1a24400169030b150300301c0303d10440000007202c58105204481c084c1c50107400451300a40000220740341200b607041c1c8410070542d00010400950b005503805480b40980c000c151150303404080c10b11152903501c14082c1c0300c0704c00044c082044644002801c0e602c44166006a61940c0d8000005400328a81652054102419030740c0076403084080800d0400350621820b1030910950707848110003545d4440c80000d0740640702e04020a50311040906c1421000d40703441c40755801b04080160081031021040c02c20904849007d88114100b0540420900102c0d0f4070040c20361078071514003c81011a610307161170020380d00f10403124103150f508041e04e01031040d070b0009440007424040c1c07007900e5103a444041c12440000c0c0400c10b114242d0024800b842c03c01e2055805082c13404444c92011070142c600e1150119400c0010307600030300c04c00400b49a10520f0348461202040c03040f0545060304403a04000d8054010024040c400c408041850305100031500d0a4040d0f40017401c03c032068 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 141511906 1250 141510656 141510659
    0x2906090a0f06030501051c032c151902010209010903031809060801090c05011107060e0316030b1006141207030f050106051e04030b041b0e130302010b12060a0b0409020307 75
    0x14050403081c401e00b846040d843c409000c0c4c0c0b207034856a0401c074543c507462700c00781c009500c3c0c00308554152004a0311094010741800155540315070b001200d18160880d1a00e41d240220890007940300c031951034180c116031060080c503007030340d030001c1180e429a505424900707801c64044084200b01c02c201d8000c41c1c4000e00b030150026600e941504501991840380100c041d40d10744850046915a080d000041c205034480f840400115000780061020b402010741a0b5030380882c044880700da0710460758400c88480c0c40c2081000500b22007000d0220140c449450b1084500e508081c4240c003034015204020710105c00503004c59100350095011070615000c5050610666a4425010740640c12010004141804007101c60348a42d00e920100c4003074035441810460141c94a41b110302003050080c2c030100100a4000e00811030034184000380c3c0c4200e0348407409201a1003503242c0242554400805140505100100e000c00700340c01148880d0322290448000076145401800500501601d900294150150880 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 141513156 1250 141511906 141511919
    0x1d091207060c030e0d050412050a020303070c1505070c1701022703010c0905030712080c0a0b071e090e0c090406030605070305090703030f0807110f102906090a0f 71
    0x209041c22040b98504005288080180c25158402c0c5102d036000214100300c00e214090703007041c041088601800481d2001c40c00e0741d0129242d580001800e8806420704801008106c0400030014422480c900d007039424184c03255100f00c1860000d00900f111031603003c403681141103095065841051640741c95444110f00b103403480c81e0760001841824000e500740300d85944154002c40b004000c031031024000f440814a4a90103204110000504a419110400180b0000300b8200111030140b030251141d0807680c142500050042401c0c81c0d040c0c0001c09800c0d052808071a04040c10364221983d0700729595040d07070b645403541000d100e40001198050324048012050101a5000342e100703050300c4d2001c0001d5102c3e007105695a6074a0312004001075000c0c51900046d0b0311400403260001c6050410144442540c25480d0a00c1912010840550310140b2640101701030b5000350b1842020100075115101d1110041c080342250080d4000e00580c0001101c0c07100b42c076004030f000001d000804009034020703200c0ca0f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 141514406 1250 141513156 141513161
    0xc020907030c020f0a020d0605060402041707150f1b0309090c11010606020f0604120c0b0408070b1f051c05010203070f1106070e010309020d0b0a0207050105101d09120706 75
    0x1d0169005211360904d0401403200007604c100130076002080030000500300d80e18100648002400650826000e001c000fa8801ca4505003030843d4a42c0009005424144500d4014400c140c1c2d01450400845080d94180150480ca50000d08403210720003a0203403040341800e855480d4141e0103501518901444004503580c40074012203100c040c28001e00007a83d440804070303661007407070003031290702c0c2c0100300072800140f0071032620780b840046030821070080403103a1140741c000d140403035081d1200307000002e07000104494000b04a92002568141481c40c81e8035081088449001d4010940640030400c0000c0040700050f5a4002080d4000000c1d5070764640b441005141e60040c00082000c154041d4401c03c00000100c4c2c250310070021980d4426501c507074600110058608000b00703903000701e000200c003804541c100f403000d8480c4062506c05a554580c170f240c42e900b1a0001811640c0c0450000d8091214140c003505c003803c00210740f0920f180d16202c10041c60b0502c15503010120070041d0000e011000c01035240c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 141515656 1250 141514406 141514421
    0x204061a1e04081e160905191b0509060d18050609010207241407031521020409080c0706020705090a0513021c05061504060b041d070c02090703 63
    0x21901d206018140c140303580540983d000702d240c030342c00c0070030385010500c20302e07160400240c3c1c41021220f10b10105801e890b07000c0d4140c0c0001664940b11010070401c2e4420344010402100e010303c0030420715101c0311740d0528458460312440c040040008070100c080d5a007600f070f0343e400058014100481c0121059000381c1d60102e0358103e585024000014840a40600c25603c2468000e0074000c5a03100a00c400e80003640703120310000e881680c800c618a03111084d01c0b460342c840e0805071000038052000840b886400d246550180c07251a5403d150008004e02c56005201d031180c2c16180480c1990b42482e004884d400351003c0701c04c5511400340300003207007030b0b0009000303044541c01e4604492540b21600d00d801a6841201c03a10310311403040c40940e00504104020303240c100c1d071941c02c1444400c44c681d2118140074055504000460140b00780a405152904c5984028841b034000207141a14051a603100d0007000102610301d01e0b16030000811247c000e01c540445140d00401c402820b1400d03400160092541 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 141516906 1250 141515656 141515677
    0xf0f010c0b10030b0c160f02150a090504060816030609021c11100c020f0108040501020c03131505030412030504020a0f090c080f010609090f0f020a020d0e04050606090d0204061a 78
    0x140081803241e45179900300e9152400305e5004540005098489146010703002104036000301c18603d40d0f2045e032020380094001480603640718203665181808100a5401603009004150010710083e08070002d145040821281e01c01408200041103000080d250540007501d02d4200e0a01c1c07065008200c0000190040480d0803a170300c2410a000c8802200d0800d8400c20003500415440310300078082d8015500301d54400d100c0e50001d4a45105004840d04580280d0910803075641c02000a000744441c5030780030781d546c180c02e142441c11071034191150041100005105001c0c56030b200080303415034503400d50420180c0f88030302c640e029056031540e00c1001800e540007043c0000c0d05403008070707682140c402903082c1203d90315920712048d2130900d40c080740140304220032150129501c0b40e40403d10302060018111440880c0c01401e900d843d01c80c00503000030705004900344a2480c2c9070403c400c0d9a5104242c41060501740c07481a81c007085407000c90010700194025643e909001c1c80c0d1040400a85801807204602c03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 141518156 1250 141516906 141516923
    0x3080a050a030c410406030c0207050d051c051908041401090203100f0204080601030c084c0501030c091107020d02010e010216080d030c05090f0f010c0b1003 69
    0x1078000200d80031343e034020000c520f110f071008240d0b02200e4803003201c1001c018015202d904001e031107070b603036407890b440b5902144c00700b17882d00101f11a2036014001d550040000b9101c0301c20f08049542d406450342a40701204199504c4950b5020314144624191822041800c081c0326602e40c90703030380103000e501088074215019002038040c1011003c0c18064100407542c003500400d80000312108440107800c42c5030121103d00c0d420712000480708010880369000314020300b40002c40500302000541054049140009022040400c00201408040c40706900e6209100c9490002043d4484100007043d44d1034041c0110f42080000b01c03d202c0c25108940440e80603030b60401004640702c110301d0309402030101c061b5000304804001c038095405001c5401e0314000520541c2ca03d020380041e0803007541010f400443c025170040710800c502c6ca40501c11811101032a0504a013401d403c440041c2a140000e1101c3d07004030140107148441da4002c01904001d142c5c020140c0e12540340801d00c441c100c600034403082d14130740c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 141519406 1250 141518156 141518171
    0x10080610050d0f2913020901090b040b03070306050702060924060d1b170c030304030206030603032703010605011103031603020f0d2a0909020304030e0603040501050609010f050310051003080a050a03 87
    0x2444c450071000c00380c1c0a4200d191f181e02c2c100b14000107104d111941c903046510b54000c90600d5a00340000d00245110320f000145a003004003000f4a8910700602c47c01301940031501003040808140d2003030319400141070f08000a56211030202e00000a4148000c202c950307280c0301d010b04000c4440c400300c01e90b001d043c0140c64800c51070540d15650301040c54a1034145c1c100700f10030b0015040110055601403006401c4905d85140300e13490350245030400c40307564510382120071f18001ea442d003030041e20010107091912910405075001007946a100180160224a2016030700c4a51203001e80c041d02d0080d40720244c207a444094120001c03003d41355800108059413015194003400144030f000300c0540340510368802c2a1103040418410007544054425014010f01a100c0b400f99683d520013148030f944a80c00204150500d0740a010742c491040c3c0000340711806501003440340381c5000a0101c1c40c01c42e070307090104050721413407410094141741d030300090085440041c072080e407941c00134014442c0c502c40360f4007001000c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 141520656 1250 141519406 141519421
    0x90c051b0a0b0c04180905030c0d0203040906080109021e010309050607050702010210020f070f030e1003091103010c0509100e1306030506131104022101090510080610050d0f29 77
    0x1344504d004441117400380c00c0008a000c04240d000740d46040c41402120720300301c0700c0f220140c42c10142e110120010707880010140941800d90058500a0403d000203018680e0240d00280081c6400004039030080118881220300b60f10903003000d9807154021095070b0741c0303042c4108020301e0f0b64170000082c1e000d4414801461091440d03842214450340001002c2c2d030900409980e01250401c012405504200400d544490b840e5907890304030b0ba400d0042e45000412952500c1c0c141e06440a000b1128483e0340351180c1d1000c1d454100c800c80c0ea80410841c1d000346982440f4101b500c0e0300404084480c3c002d207070200d829450750311a900c52401e0f00d02400c2114041e81d10180003034a112580c800040800b0607031103101030641400d4010386920296034420803580c100b2408940d08071034090f03020041e455111001c0c002e01c1d41c880c50321100909540c5e0060034a07480c00d400c0001d0485018400c00e03000310350310801d03030007881403070f147d5208402e500501c011040e296600c4642c041002d00d40390b00d840b180c052808100e0785c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 141521906 1250 141520656 141520681
    0x5030907050d050f010e030301090c0c03021b0a08030c0604050c09070203090904080c0d090f060c0305040b0c0c030d0207030203161508070201061205011a0409020307090c051b0a0b 79
    0x248801001803010608140034002c0c07100031400201c2e00e92144c440000308849081c0640403000180e240103580300e40c50a0f4ac108240e8141d4000001444084e008000110303034041aa91481c8205400d000c0e1110b8102012803100e80f1035074071071009800003180390644003602107401030043c1e014500302d0f48549450310412050010070b48021003d030344108241407503400c20441d282e0b403150242c20000e0a0201c2d00f41c2450900c0e50445c1c0200004580e40400d21881820754682070140010303180c60344446910359805000e034807460081007102d620124007007040d454101301e00258500080d0a403000030a040344003030b40d601084d000492190007454078403c9211011344044088a50004003074402c407031014401d44d110803001c0c1000c8115501d81d1400305020561a0302d00480c1d520890001409500d15901c3c204130001520398540700d241420303604405640c000a00ca0150f03400803400207444c040e111000c4d25540704a052043c3c030100d010003592a490004945800740d00d014004420955a0704010000c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 141523156 1250 141521906 141521911
    0xb0f01080610061b0204090f0b09010c05090d0203010902030a14010c02030316030903020a02030d050418020a050a05030916030b070809010b060d11121501092304020702040b0a0314010c0503 83
    0x103070240b50070300400c49144a01084821004071032442c480049498000c102a1400c03400265941405000c1ca00104094108019070000f0309000821000c100b0310001441c520601c10014861824100582c00795039003913111104295000b002c9989101851411840c0c038400926840b090354600703840f2000150002c411240f0031101c00ca00c5007071428003000141d0041580c02d00540440c41100c481d100180c600300700101a0a907a519035a4486103000c0300e050b100c4104040b48482140188007480e400d903000030035180e6a01140c10900c1c0ca0399903030982d40d803404002c0c842448100700300384400001d101c4100000c41c0102010340e01c150b540d0792400c4045007a00e00c07180116400a00c05c0002000102007540128000145001140d25050454a01600d4000f054400c00c4210f00a03402c480ba1075a04016900000c2005461454120030f4020103808030680c0c0c031000c0740c025a00003410400319a0b940d4043e9000c604024003400d0401d0b20781c1008101c81a502120700019840d100100c02c82c58000c1060301d2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 141524406 1250 141523156 141523171
    0x103020109063203100f15031d0102070804060e060310090c1725020d02060103031803080c0604020319020a0306240e041b0612090206090406030b0f010806 68
    0x4050307864000300f12400300744003c6660840300b402c60404658849080c01100610440c880d694032400c004803540044a020382c010140c8900f010b4040001c040a46200905154181000290000c8104ca66403030503200007041001948009008010001403c0c0940251031540d500d4494048110050050074481075409544005503000d04020805143e048222250b038035190420074003421000040b5100c205481140501d50303030303280350f04172001e40100d14a11403e41d4802060100ca03020b41c0a529440c042c000a42002a0f031a40c2010921580e0300d08402540c0c000c455a0f51180d44510b51505c0781c0003034a040344640a81d40c10f2100b16041500341554141c1c0041007110740074030307581e58200102200410003207400f000c0c5140041008007000400b00406902500c0304451130310745001d0f1080c411a4044a1210b04901c009000365a400100c2d1000c0c152000e80002d42c0b8546800003135040d00070151090351290600c0c00c040100017585e0340c01c9001e816000a03920050743c0f900080e03034544508407401c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 141525656 1250 141524406 141524417
    0x5060f0105010531060c0b060f0108040308060409020901031401050c03070f1809021207030606020d08041b08030a120b1806091308040303050901020c0d031b06020f0d060510030501030201 82
    0xa4581c802084040c8031800b6104c0b0041c1d2a1940505a001800d43ea8042000308900c2483d40c814440d21241c101d6000740e04448c40c0d6221011f4400107010b8081c060009001c10400c50002030b910b45880d40b003201c4543e0001c000014941c0c1d6450f2040b40c205201200d900316508000c00f282d0aa04504196030040d852502c1d2603810262800d030849601c0340301103a50074194500300001441084910040c00c0e24241c0790f140c0e4080e460b1880024040e1101e07588894110b501840c2150b240742e5001861a070006d5024036940784d40000c145161095402d141c11021341e031300000525103655a0841590703040700b260303090b003030003d40141e400304185881880120100c203078132040000c1143c6403c50005510802c0900b101241807032035140d480395500903030811000700c3c90008bc190f0043d07030100401d0114807402c44074107070b03500070540d40100b11a41c03020040ca80c02c000030786004200049601a10b210408540360720340c07990310003218100600014450680510f9866050384030452090089038107903501a101c4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 141526906 1250 141525656 141525667
    0xa030201020c04021305060307050901110303040c090903030b090c2106060f0a020f030a030f0b0618010f27050117070203250206120a0b0303040f15030e0703050a05060f01050105 78
    0x2c3c08042c1d8010000c04c22001018980031030150f0b10b520186008240e5942c48607101d00310b00001406c441d40000410340e295200740704000008022118800c1950360704940030900032200d11302507010700b442041c2d1071f5000446104000c0c0048000d80500600c19440303010140c800505a449400840151055034204608009444c04203414600500c00c0c1e032620700c111000280400411419a04050b50403c0013076116200f10990000b5405203031b10f030307070340031a80c282c40c065240107480017030542188810f040c17141286446001078041e041d125140001a480170002e00e56517000c105800006003d043d000c1540c0501017039408210014251107032946800451070040b4000c00c00300c0070080e200c001d00b0001d450740503041c01619850003600c00100c107000300d90540d007010001802a20b44a41009000382d10620007000b0740f0071a1007034402120302c5040e01c00a0120300c424224042e1010000c400d030603201e406000800c00c103000403d550418024015503049482e080c2030950b0f010406c2c0701c0c4600150f400d210 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 141528156 1250 141526906 141526909
    0x9070320070507050a0e01090f05012d050a080f01061d010e060f04111308011b210e070305010b1f0e0111190317040b0705030c0705010f09110a030201020c 68
    0x1c1c80924094000c58150569810010316165000e400641801c0d0b403010042140c60003a018000c6c440c40320f00d006110a6041036041c1a02c074180c03424101c00c08030891020007848601c64882c0d1301500d0f001d03004c40011619180f000c0c0e9a40d4150401c80050b61800c01c0008070715805000d101d10000ca180204100340e4a01410244c0400d409004280d03c00421000304d61103942d28030030302d1103940d03003220066181d400d910060802040240d000d42440e03410400907610a070b2401041c40e01032001810200c0100328490302d45044501c0c0c0410490629180c20720b044800e03400022076004480c8924000c1c03020304911402c0c481e10340c4610300303064000c01074481c03047c4041e80100c04003008140185003041032201c00300e029074509100f2132404c1c032040c083c0c604541c0c149580300d00b901451415140c403007141070401e6030f100c01c0c100c40700800c91402c112011001c1151410b40ca02124403840e00310009020b011145000a00140079080c5c040392501d58a101c000d400e82410613521045035016005003000c20f89400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 141529406 1250 141528156 141528221
    0x608160801031b08060709061e02030a11030702060a020102071506140d05010b0405281a0f010c0b010605030f1302011d011209050606012705010c08040b03070e090703 73
    0x40c02c81c4824000b0f1008100200c08003e854414070b5030395030f1a0b40e0a4a000c2004d004010b0300c1203002c60000588012002c45a000011203602c1d076000e20b0f00824048049103400d01354021190300a502010010b840450310750705402910840f80200e10080e840d1200689100407035010740300c0c04c521040c0201d140d00b441c1c50000c04901803280108004078400000100140c00c465044402203440074802942015078402d14840e42d0a00d980504100f10a15a544204101090743ca040d0741c420b080647c88014513034800c050550b41d907907200000c4551540c440001525a0b001121500103c00c0283c00044007040c1400f002006207030180c41d501e0200180790300110f40c81d05001e4840f0b0622406c80b80154070425284a05003110340a10042d04081c140000014510804401010507070f51401c0c4509020a0402c580170f022280c0034285202c0d0a4001c0c50701c0d000b1750090340c0c0001071034035020080000c000e80000540c413100c20704550340f120355903500e9010b0702140c4141005c3e29100e035902130300d83c80d020307420f1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 141530656 1250 141529406 141529433
    0xe030609070302040f0b0405390d0e03190806010305071d0103050a0b100c06050a0501031a0402010c0c08010e070602033103020301050702030c0d0804030e01051e030907060816080103 80
    0x10200455070391071b0400440c0513074000b0f44c0c414085942030100c1c6504c070003808183c0a9009401d8914101041059020000e1805090041180f5641e10000201e0103d000c200711407400d090765140d0040707062441005408550b00f1900580400d040000294400e40300c1c4880d0980c070b1411b0903405220301c1e40000114003e0500a1072004144c2d07903010740d0125591485640160148070355180c031640e000f1032400340301b50f600140054103000d00740001440003660100c150060541c01d8a0720108581d620300040301c0c0c203949900081c1c6a26000240811070b10010b4002c00555481241200c03072250352403004036501c1c03085000c29400a414421561100c0c0b4105401507008076408000c600107030348a0f000030b0708407101a00d00401603480001d46200100041c40b200110344028249a0f1451500e901d0180500012000c0b640c100712000803551078142c1c0c1846042c0c864600c41a8103a1a4682102a240d50b042d41d4000c2c07102140c005000a03103000c40031400020f0500d0a035441c40800d03446d59403400c003070a801 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 141531906 1250 141530656 141530681
    0x619050c010e0f1b06030c0f0a031104030614090a0305160204020903120418020c0c011407170c3009030304080a06060e0a0b031b0406030803090106060e03060907030204 74
    0x760007103202d8441d4100070100041c034051014011020744040c103040464001c0a0040c0154420300c100301710081800b040da400c2032400e440450b91503525840480040103a4003013246841c0c00480c0100500200d0381c001e0210f0114205a00c00c00c1d110304081c1a59071081c0d800080c001802000350482003c02c491003c00c83e41e201500160502e01028000f905000b2000500a01800041410000820440d1680c040301c4100ca004520344000800c043d500d503514a4651810301120225050581c58000200c031641c40e0418601102d05111504403a610791104440e2055031240d17040207541040c1110b40e4082903aa0360701340074600050b40340d50f22810340200f2011581808140400038401c0c1080c080901c116200d0f40b8001109401c100d02030f9190717400500076124491a108062540c1d86001079800c44900310100c0000302440035074001000361605070401403145d2004010702090603815005082a40d80d19250249840700c901c0505503150130441c0c12200c0c0398040070042000d401c2590084020340031 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 141533156 1250 141531906 141531911
    0x30702100315090e0f0c060c0705090601120f1e0605010819020408032206140702090405031c0203060a080c0109030807060f020a0c0302210f1305121b0619050c01 71
    0x103031510628103d6038039400c2e20513540c000d601591075400d814844010b0075442142c0d010f06240c1440c01c2c540d680d450324041c0718020384014020803d0350b8004c0815900c104a014800e10810241443c00c07005408504a80c8450001110303080d42c1801c26405040181d41041e911078640360b4a810003140b0010001400300f40c000d07820032010450b0181400101008003d00340e140710304c0d007515189011000803d07480041000500204a1801c00c591001c407081250111465052602c072810a00c2c218410341b140740c50f40034500c51144a59017a141c01840c440e04040316052080d5540da088161525080d829060002d540b0b50b50500025030100041c01100d4000c40c2c002410b0144080c0e05130883c0d05c410b80301000300b1303c0c041b500030400d5810002e51244888140c1d10302d0103029030065041e10340c02200c89503c9581c101140c07102d1129403008080000340303c002e10709601c0c40064141a611034011000c0000c9403116050440050305210381261061a5900007246030b40a100e041159507402139004400c81c2d54 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 141534406 1250 141533156 141533159
    0x901030c03110a031a060403030c030807050304231006063b0603040309050d03090905090d090b07060f0507090e010e070507080c0f0d08220507050d030c0f1a09030702100315 76
    0x45481020701f0146200f52034180f501d40d41414090100840207000f4010040304004003c0025010925810369010801c8a003c60a82d020740080c20541580b844400051500700c001880c10f41c03280354010716030038400d000010101001959015441e85040c0d100003600400820412030801c40c004683c45400b03440c04c15545611b13030001441e145c41c07031030003900000d0030048140084501071103070780d401c0f90100c0d0041403d040c2c0300b400603001d07600c10312030b481c003516010035031100748801ba03002298070f441d40d143d00300400e03d03020303402a083d030740c150045100b100c1e034040000c903d1043c0002c44600407070341ca440340d604126a40d510030300c032507004c2000c0080c1801280702c00418010200443c2e070802d030301c9441d1050286000d40300d600e42c9d04243c05c0140040090030744520040f46000c5070340c40c107807030003950903c40e01642810291550512940010701814161400d001441100034800404d80303104200d1001e40d2f10b503101c04d05c0d40d034007400001a40c413541d203448200445019500c5403a2542c0302c030483c0b80020303 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 141535656 1250 141534406 141534409
    0x91113090b0f0c0c120306010f030b0a0b0a050c01061e0503030c0c13060339032301060510170105010509130f0609090c0f050d0b0403080a0216080901030c03110a031a 73
    0xc0e43c00e068601176010041c04110340c1c100d1038030160030b843d81c5000c00c1084000300c0001c03080c841d64031502040304c00004001c4d8045104108030365001e401000203200b49542c03202801681c024943c0102c2100031b0380c020103e0702d4a0040125406081c00000401410f60007a04000201181000b1413244039500d801c000700050030717520b03907000902d00451081c0e04c1560503140780b04400300400100611f02004542400010040c404681d4507031801030040c1d102c100354224260062085030426688450324405038802c60340d1000c084503c000034141000440e90340c0d000191070301d006402841e030303001d0039503804000144880d510444003c0200c0b48042107244c0c0d03804441c0100d07841400e041d40d07445180036003409152448028100100426501d46c3d4081140e625001040310740500002e042040c81c001055604240340c0503100c0d0705040e101e6055581c0058138040f2081d91001c1c2040c3d0100f82024600341c1114060b1140c0c540141c1c4030b50800e4035003a8000b00860050444e900010b40c1a0192007900550707 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 141536906 1250 141535656 141535663
    0x130f05150a0807091215050a050105150904022b0606020d090302060a0c0c060302040509010509040f08130e01090207110f0a060f021e1e0105040302030403110112091113090b0f0c0c 79
    0x190780610381030420079400700b10364021f5400040642c3c44113410000100318507100c4003001c3c803025412025054480701d0070000140a44107191007000201e1038405032885810191242c0b1551100c0b000c4c0030011a55038040aa859001080300080400c02010041016052640003410740c03548a04d00010f9803125907540c820719800f103802c4000040d40c042400c1c052070601c3c5410074050701d012500c03100c80f45010383e520704c003074000403a004000c174801052000d04900c0604000d070140803200c84441c1e00c1e42c1c42e0b6003004000e400c510b00c1990030306402681d004c0b2a04000e9642011494080c02540c842820030000362000040a428007085200341414408010045000078002c030f40c8100103072041400d491100344109400700741d00d074440d0745050140300000360000110381c1103992220740d01c0c0c600000b080042c3c44a01c0214030011803103081540e890104000748200340710036002282c2d180e0312220420301c00d8089030400c0340d00a08903407602c40810300500c90314503e5540400c0c1c2e018110700d00005e00078084e04 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 141538156 1250 141536906 141536939
    0x141306092003010c02070e0a20030108010b0a090e0c120c04020409360b060a0506070b0402120a02090c030615040612050f0408070204110f130f05150a080709 69
    0xd101d00715410a00031441c2c02c0c010b8491340e0406100a0810b5800e03c0002428004080c109940583d82c071100008810200d82e101c0342c14002281a840c1c484d0b9480c98001c4c040d014401040703210351924100425100f20a10820901502c20401041c400c0c0c0c4d20b9092111030104040081c14501c03d000c4045410307926400200701400c400c88001c07440d0160315100a01d90b0746e050910640300c00c20074010005003e102c205030680742c1d40188601c549a141d103004140c450101d9000305801010001d07001c2c4c01c5c0210755a1701c601462090720300d6140c8007604003d035034690702e4002c2c009511403002d0000c2002d103102c143c051074000701c0c01005403041c0b081c848101591540139a010b500400c2e13004826000f03503030052089591100d4402c440f503420f40780c42c4ea990a2503110b4498002d22035a99a070b240c0c540c48203600259000001d014800da56180303034868145070f89036154441d4240d055050100440d6605200c1401c071324484034428041c0c10221007100c00e0312540c00041c11002045091107000a0f010710121302c442 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 141539406 1250 141538156 141538193
    0x4020415080c03010509010c05030a0216020a060e030709050105011704110a081e030301151817010b120d08130807050319030e01090c0614040b0705060601020d0314130609 75
    0x2440b0090060609488000b406002c040e407516041c0d1419980000480c1e9002c1d210090059496000303c0022010f002c1c5114081e400c9030340c8140110360250001c1c03444d40c96080272011118410343d62075201303054034400d014030b03400254440c0d40036030001210704901da002442150862001c4104201044032075080ea80400901e41c080301880840e05c0b80d44492000403242903000c1d42c076560416003c03080a540001000e01007085441d0b4030006440e00024442c0540b0141010a41b0381c152170080501030703c0c001c2d42c914410090301408180861001490203d0398045450702c04403a0f40381c2191140c041700030b03174040d03410b0b101c2000184c000130014402480340440070425040c030b40001d14002401c65000f4484800b007603252900da1408940c040022030101e490b80d02e03004034002601400050b140c0240d501095032403a01103800c000304000070a060b8030590084e0b089512440e9035203021410b8545540d0410190400400410000c41080b007103961514010f00000c00c812034540d4424143c180d141c1c4941 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 141540656 1250 141539406 141539413
    0xa0305121207080103260903070602010608010c050702091b0403120306060e0105070302060a0203060a0b0d0203061c11010e0103020906070b06090a0903050301150e090907090f020c03120402041508 86
    0x1200403900d0544160b801684514141140713604540c0d505600041c081495401c001418000c00e0900244004842490f0406070070b0700c954941d00c010290280080303000b071954a500b0428001c0159126106032000960010890035140c0c0720b00c3c90010038500301c900000409030301040701001290328820700b05042c802c5550000b801502c0c000c030081509030030008960400000708024404030350b0005000b81c100c2c052010040e502d8403618001220310130541e2045181c0f0300e001c00e90600c0c012465010710310400d029240307025801e01100c14100c2410701306100601126803280d500249507c00c0c1d61543c49424181001440c101140c070025295403c19001140d80036601e4040100b90300704843c00b1900721911000a1110503c0f564002d880360005004507a1040c082c3c0000d1410380348109525540803601400001080c00d040700700769200c100d42d0240c0c240707207401e06d540c100704034a00e0b108445000ca070810203542406204410b4548088014200380d900540720941c9500e00310100c0010001021040d004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 141541906 1250 141540656 141540667
    0x3160803010914011211010201180302210a0906050901021603141218120304030206030414010605010518091f080a1103071203260c03011d01030305180a030512 70
    0x950140d0700a80c3ca04001e004154004101c1c1042c0005030500e0142e0014040c142441030000403030040c510583c181002203007500c000b4040c180c02080c8000d8413200002d05000c41040c2281444c01c0f8820304081c2000224582c0e803c2102920075009400d40240500c10394074444490301d15034075030300000e4206844c841408049014030304000c00c12502a070200d21891800c1044046c8d0500440b0b20916030140034000b000341f40243c00c50140b048801a44d801040c060300c82c1003908080d50603882c0c220310458590329101740452158000d0301591a41a01080d0786801e44041c007060060aa1026100c074030301400041c449125030304003803820409000448010054070040b414602c1208030642a03a9000b60030072a410b000c102007100f881d403402030f098109240c2c2d07030034000201703800311a407082c0910f030250030f0780180070300d91015000550490b10400124545003208400d0031000303500038030000340032031810401e410f0224160b002d0b4680c2c4050052405001a07665161281451400d0358000b2207141e0001c1c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 141543156 1250 141541906 141541919
    0xb101b060612150e0c010504120201020a120c021206040f0602160606060201021306141b03070b07090510080f0703050901110d0605120a150f0603021f02070611030304020f030316080301 81
    0x81c130210310001d4004100f5100000000b03807140c4130f940a20000010000710300001d40e4000c0041c4100c407076000700e00c3c00901004010003012051442c0d0124440e2800d040b00170a0480005203150280e0380116420165030065a540e0307001b940422440041c6501081300702020944074031410f001010345400160380d03040f20a004441401098200c2c1042c009084132010000c214082035622080c06000441030030ba603201c0b0000c1c0f941c014081c005001c202c0300d104120019a10003401811640c0c15907400060b0031424004ce0307021141218041100f186034000911203612070b8006540009280c800090862421848200300358004e0460304840e9481d01010403081c18440c582020f89900d281c041c184d560500e40d10820070340324000c589103a80b0740f1900c44062514032584004000c41d8010003502045000c1d11101344261281c01505000d405020300001d41d06000b004031003000c000002c007851441e0780e558200444010352801154040c1300922400c3c0e07a140c840b6401a5826005032103881c0c40350701d00079 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 141544406 1250 141543156 141543161
    0x391201060e0610090b090402160609020406121a071e1d040606050d0f02040b030906090105061e13020c03340c0302040504330b101b06061215 62
    0x4110b01e003d220724001e01101c0715800b072000b00c1610748501c4440d07580d004e944009406400b800501c450400c20810700542045666805511214070030340382400305070365940700c078a10805000b030050039030072061140e0100070f10005603203540034105051003101c040401d0100174840c400007500c13501044010f48280740001440541708061141190280708450410100a041e4007030880000c200301d8607100c060043c2d408030303010b81d00540b840d031144c20f481303161035030081c1e65900040c0d546c03d002d5441c05002c5580c604200380c410080e40e154100310b213112003924091204404404800722403075075081c0031044009100f80000c240010030340c6210010b4a5403942060200880c41c540c02e0080e084190305400080c0541002c541140d80454000500c1e070750301e0500c0460100c00710420541d140d5924090390810714a840c264250720703d003000070000f0780c0d9428203100c00c0ca14600712810115072003428264600c525000c1080d07144d0f1052001040c4030341e0f00c0185950705d9424100c1117503209030700c07840950106802d1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 141545656 1250 141544406 141544411
    0x1909080c012003010321030b030118060b01030501050306010b0a1701030303060303020607020f06070509011803061e1107110d050607050406120203060a0b0a020f1204051002391201060e 81
    0x100c2d40d24a10751550b40e40004548800c134481d203020706500200a103240c043d5002c00303140d40020b002404100340c40b506215400500040885801c3d04d401001e0700554400d1103114180c03a0b018006018690801036a6803c0740c1181c8a844104400007c00740078450303070b11a00c180254443d88020132003900314036001e401c01100401c80c0003154411000d54036200c40000311960860a941801d6a80b44964401203035008061102e6541c0b07403049043c008200400e540c004400300300c40001c0c41d804080034075641410f481e030ba2541100f00310018480540854400038000c40d02c0f0100524020100c1c90036038980b800d01908a4001000c41c202240401886820040030b085922300518110303d545003000c001081d201450041c07800f540004941c4a61040c000c10006050f0380b030a500b2128a41002c000c0c0c1c160315402801028060040f41143c0300100e4000114180c0490720941f9541110710759004900c01d458402c1d51901c024400c8201c030b1001c984407064030408020b808000400c2d16401c1c01c5003004848400b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 141546762 1106 141545656 141545711
    0x11a0405010c020604050402180913030206010302091f080604151416141803160503031204170307080601030b090105060a26010f17030406081909080c01 67
    0x2032349c00c0c1480c81c803012500d40d00541d440500020170241d031070100902603413100c1e0042c00185001e11b20359501403900d0110310403404015140400c80300329035110340314075006481400705201c444041d01840c442125401e1120b000182c805c4004000024800b000581c40c150841280c83d215801c0454024100500c1da525500c0a1700e0030300c510202131804500c01e1040c0040d010044110400c007004907070008010750f0500c5440c101e2120340c0080144201c40f000c1244e0008100180c4a1010318015000c0d941d4140702c9150100004d0100d5281401f10b61081071143c00400241e51940c0071a400460f082c9455110000d540034a0502d0710174458041213810751101c00801c11070091020300c021140380c06600300b115070244010340c3c0c0301c0c8503602940002806680014043c4510440740c06c14101e0b80e001d0008004d1110b03154007a40d500013111288169460701450810704061240641c4030800 = true := by decide +kernel

theorem cover : BRFrame.Cov 141366906 141546762 := by
  have h0 := BRFrame.cov_init 141366906
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141366906 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 141366906 ≤ n) (h2 : n < 141546762) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
