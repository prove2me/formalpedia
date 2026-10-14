-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0878
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:22:14.97971+00:00
-- url     : https://prove2.me/submissions/30a121a1-466d-41a5-b17b-279fedd15fd2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 157733812 ≤ n < 157913669 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 157735062 1250 157733812 157733827
    0xf07030b1308070b160c110d030e0d060f0506010302070215031509040803070201060b1e0f090406120b1015120b03030c0f060906010f0e0403051201030b010e0f04110d08 74
    0xa219030000c0c030095611510400c10042520a406501070030411175180c00b2070b1782c82069480c0b04885100c2e5207114050000d92540c02c0030140122070040120600908658802c2010f10308440501074200783d05220340d00340b1012035502d502074002e03594050b5005290b10591901ea1110751101e805c010300b00c42c0b4840401800301415221b88051a0055018001850b03882c604010040e082d42c040d039002102e554010042481d104405100c595801c507400c0701e109507182c10703c0500d00b066001d007614860380b00f4a048400944014160f50403460603102e9044000c80350b46164002c1703020111403003955a4491a00b0b105040c06200b804180c0851420f5000028503400071000300c0d156400c08000603410707610401010381d0700c5000b082450340c00489030b401402d1175810000c01aa403884070388502e400f2120600049010580502c0c03d075540a154950922850b43c0c5d2401d00044c201001c0c07107031940f50144480400c06203e00401c110b845a5000b8444949818440301804007051104034107861885052040c00c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 157736312 1250 157735062 157735073
    0x314040804050f010f02030a0f09030506010b030f010603050c071509140303060a05040b0a03020f0a03150c0e0301020a0f080606091207090b0607170a1e09060201060501020f07030b13 80
    0x150056008600480d1100e05040030b0000d41462150400c1c140701c0382c1c2c0c8035482071550000881d4594900c40c641001d5401c00041c2c2a6038100e400e0b0001803e90081c42c0c0082420031014010b58401da02c81002d58503566695401902241c42c145e501040a1504000c1f410100b40d501d19020001ca105110006182c0b400f6152307039600d801052596460780e040041440707501d281c00200c0e0b4010304422034042140d07215003000150791981c5480300078054001000c1031300b401d50700c0045200c01145c201100304d00100310740f80d4410040c0380000140e03000c0b455032003019806040500c260b52008190342ca452002014444003515000c80041007240d020104003c00391468841a4202102407585401040310b50704103500d01c42070350400066a80a400144454000f0031b0340c243c411143d803c180c0a01c1552520741030401c8580301800341200302c2007010150740506280e0302000d07180441c1c1d0303194001c20400d521200120307254000c44013280c00c194002030060012030003d802c540d81004800014410514a95a82c03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 157737562 1250 157736312 157736351
    0x21e0907090602280609050c09090106050108011d070e040f020c01050412031b0e01050f0307020a021f02120306060d090b0a18020108010e10030606080d1106071e03 72
    0xc0c0340001c1c1d02003402c010264042110f031441107103514185603020300d041d4003116040c00d040c1020f094603403130700c0e2610180041400840e800150240061030146041c0000034068a0280308407130014024070000100c6130700a117240c00101d54035000604881d02e4494003100d0b01100d01002035801503554010380500412840204802001e100010500d4582400d002c50b40c42128040d0b00181800d001503203541802802140c6005581c84c20181c00e09000600100d400d8000c44035400000200001030100603900090350810f4a07208491041c50703040e0a010400c000e9030007650540160b4828000035200c0032044000d107a02c0b10026007198213107094a41214243e4815080c1503c4010305881031000000300790066268880328240303003000c40c1c441980001e101ca0014454100780f850302201040310102e18502c21001160072000503c14540c50301c80d000c2d01c0d04114002c4d2804111303911841d00c11141c0106940e482604180c4031480e007042161a0002c4240058022400700b642d03a21840c850b800c21902c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 157738812 1250 157737562 157737571
    0x20306030f1606200304150302070f0f11030c010e010f12060b040e130201020307150e0f0c030c0a14090402011205070206060a0b2d0c1c02010b0109080a021e09 70
    0x4402c1c10042c40d01d8800740c6071075050720040000c0e444185000302c4015001044030b0403a01001c4005041103010301c0200c009002d2100c2c001c0003015800c841d00c007480034140300041c00c0d50103100f1002e4030001103810503982d64020380c0ca45000c02c642c0690110158092400e507402802d46080404100c00c440525504440da260003040440307001082c18882409022003031580f0440c1d120182c070b141c0102e500040d607603004016006000300060004615130b07450503000320803608085011035001d011203580460701c071100006424082d2040488880c0d0f2480c048400b10215200c980300d60745030404140c2400303001680100164140125400300102c02d600d50f22446202c0c1c7e02c07541c06890741d0f041030010005e075404250b0202e2406a02800b58039481c80e0005044c800a030481019080c41d034104480100380d500039030949401c1c90003045a6480d80c0e82c00d00b118042c00c02030650082200040000040d02c0c28030440c024026558040c84090300181050b0500007105010607481406502039207000a0792000101da = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 157740062 1250 157738812 157738843
    0x207080f01063023061603060b0406020a081c1e0c050715020f07020d03090e060a031a09120c0606040e0d02071a0d0e1608010e03070201120b0301020a1106090105061003020306030f 79
    0x1b51032101951510595000c1c0401410251a15180010080d034070a107034100508100710004102500840c130600c0998511000c460901c42c001244403440180042800e41030381290408120504007445070307085504a0750f001c40c10060b04e000586804000390002001c04409420402c042e00160b0784000400244c0d61013640d070385010380c0c148110101e4240380944800d002e580603c00500001320780c0c0380c00c6034041000c03e5a50115030740300520b05151800c8414640032000c000690b070000e2580200f41144074100c141c400340300c5d03400c03545013880d5501f61803800c900058010700d8041c03040c0760005842c0800a40340722041ca080511510742d541c1158180100e0440c1984084541181c01403a649000c004140b904003c010000d0b641c0d03c0726840e8452a20002d040000c0540382d00602103e0303a200c40e1420390050021503c500304210046c1028141d40b20750011445150000341c0e540505003e2039104e45400741141d8150504080c0030341c00382d00040e00c4240d15009085100c154440104501c400750031000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 157741312 1250 157740062 157740091
    0x30f0f060608010207200102070504051e060f010c0206030a0b040501060c030809010606020c010e0604030c1203021504020303090f0d0f031d010e0306070c030207080f0106302306 78
    0x6203040c100325030141c1e000721a603900520800703020541440007110940c0c11101014607412503240100c2c102005600020760091a2100f40314680d002035603240070104030610891710a494007803c10042c40921000c290001d1545011000103040210256800131200a00806d41010090005041e60310907009840000d10500d800b0040c95848000150050440802001a170b0b0400300d001352101080c54869052100300c0e2444411510f66001716801550840c0341041455211038100d4103400605000360010701c170318100c200d11041c03d150108d01665000303005514140030502480006501003280744d40c001081595580825008002074600030f110f903072140c90302600d1b0301e080b49081000c0e254590402105035040d00060324001401e80d0410014104035120b0400703440c0c00c070300e0848103400090890149000c2c4110000d0150401800d071000c0001e5400c10180d510030042001c0c40b100350907901c0295050101000c585082004070580d100c0404059103101d000807014600b010503030b01078840040b072 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 157742562 1250 157741312 157741343
    0x507140102090a06080f010e060f040603120e060f12060607050a050a02010318020604050405060d050d0503040b22022b0309080727230c070c081c0e0604030f 69
    0x43d82ca00c040d00c164103040100e400d08180054020300140680c0890004481c040f03151660388801c41040e00100030000d1090079224540302e01802115042c01d00403545d003100c905054a8034405a405820103000b426003000d0400500c1c42d0340c1c210242a80e03400c07040400c15000070031814400c010030140a40d0041c084ea60280c40018200d4503400e440d03400f04032425216400683d16201213a0407204100d134080350a4a80d64002849100e9901c8000c1641c07055030102c0d90b8098000001d10b1045008031500d49465803059150342c00036080012001a101c18500c40b80014902611181c00c41d100e01140722080c50010a42c00c3c071190342c2044150046141c0c8201040b50020402904024100c00c5d240c0d041c00c0100d00300a0b40c0b0034540500d401d00c0d078a441d00d801c08405011440755089100008403914203d09000007502c2c5103902c0342c2000d07502c4000000d400300d00440e000a0410390101940040c41c03c0b90f1410b00b044540e0040028140d601517010400040441c42c400d1701c2404040c0542d0f000441c0a21 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 157743812 1250 157742562 157742569
    0x240228061a01270e04060f020429091c17030109020d0e01090b060d1a0112061811150d11090108010f0303090b0c0f0105161115011401050714010209 65
    0x2004948a00b0f681422910ba5071080118541011036050740a0940d0580721407614002400d00100a0060b01d03201140010741010501080740c2d1922400440c590581d405048080380c3e8810703040d483d0703041070b0020300c50303c51444581c2d02d49440c2801141c0340400c0031054910061a680281e01101010360041a001c0c0006818820441031149281c02007000f00742e6503039082ca00c01401411a0b12890b40c2042c010144510010400e40c000103d02d464002580c444ca2107421801c40740c81c2c1502c03d94034020340c030118031800400c0c100002d904000c08403c101d20060401c84005000002116039007414082c1c00150003042c02441c400502c8a280c80381c03101c40030000100f041070160703c01140b2403050001000480d40000d04003040d43c0040d4107455a5840752052a480c0c24000b01c0010341c1c541c80c01e000c00080c0e214103602412141650790701c030f5041c0c0540010303c1340d40701c00c503810348003e0803491001048804504000241c0c0307920181482810300300c0e0354807203488019030340740c80e2282650001402c01d020318 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 157745062 1250 157743812 157743827
    0x801080c032103060d050703060c0e0303070f02041509050f0403020f062a120a06090f06082d16060216030f0201080406020d1104240228061a01 63
    0x5006030020000220381c0e80440d0098060038902001196000020656548130344201c840406e030010101e64109a403803404400405002015000280503851440858034010049500c15900681c1400404c9026000c00004204101340303100e2401c800100010000d2450184500c5000c0391030344400507180606004c0d083c0b04102810298982107642001803c1800544003e100b0302141201440e004e0f40382c2010429200e0030012a0a02180204022078010b180e0464002d94a41340740c01c1c0300000380410418141d441c1c034000d03c0280c1e0006501c600480719140d00c5d591074140d480e0700182e507010011186a040004000044050000042c02441015010407070128a444040707106450549983c80c2d5044200300b68000a04018050004c2411b014403501950f5480f400c4801c204a04e8080d560030322000e038024880e0010600480080d0840c03d254220240b0a8460035009059007489022026444608140c401782800c00c001c2170b081c000c110503204a041854501ea980314607445000005400d04 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 157746312 1250 157745062 157745083
    0x2010f201e0604020109060c0f060e010c0315140d08090411130f0e01030b07090b040f38030406060905160e09190c0e0402070503030619030f02060306060702040c080108 74
    0x1688860140303c01030f40e01040d8802205c4084c94800e03034140a510303000c000f001c10140080c03c8a401d0180038440d80e44e0652003403101c428103880404c013004c2180b425210304202d520420182e1a8903030f08483d001e05001d130003000d04a1040c0151498440004001402c41d20880d00c040001d140c081801000d10b80e8081d5000040d20003408000c0900703141209100140c441400b008140725101404180344e203010385608030150003a050710a840759106c007100c60600780d00e40b180c105024a00500c00b09455002c2c0410816126064135200310000002407134909684068401c441c003594840c0e0014030a001841014000c400c48189003425501e052801065030600705a0b152260070868203004005840503102d00c2904185000401d1034601100300b5035400e1041003500313400500004200d020450b002c00110312840007118604581c0c0d10404c1d40201d0b059060200410720391103080904007505d0000701455000b10020400d601c0e0400960216040c2c4824031f0540010a294000600c000e52051040a0703a0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 157747562 1250 157746312 157746373
    0x2120c09030604030c02031504051f020c060112170703170c03060d230a0b09010612030f1206050414010302090903121b04031a0a1a060702010f20 64
    0x500c548400000d44903603001e40024184914080030701c04544061240c030402c1e19559058200d1482c0c1402e2040e15581d00342000e0409812040c150502c16100c0e02c02d0300d840a45103401071400303a09102c00c140f20440026030a03542c2400394000e110411000000400f03505200e95a004074001c0480d8030030305484c001400002c41c040e018001c0104680b0340101c1408800e40240740780d001f811021998a040d01e03100030b40d22400c2e0082d1000c040070700c500480c0490040b94504000c00c00c0f107036034030080b000501c1c80d501c00a002030780180380d0400d070320b200d89408014814000c100154055507100001c08941d00710301d5282d044e010820040007503242c4401c0711a440346e4941c0c007452810714245692030070b081004000103001c02900c110705505d001014180e801070b50744114005480e03000c280d886084a841102c0007107400c3d04003a40c4215242070f003c8030140b2440041c06550400c2d105600658868100341002c0c000c218101840040c9003804c04844079960704040701515079510f4141d000e0482c000c002080ca4031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 157748812 1250 157747562 157747567
    0x5070b1e04180c08010302031b150c2a01050409050a06050a03150c0201020a05040323010e060108012004090f110f0d05060402040b0f0d0905100e24010909031407030302120c 76
    0x580c6009c910101c2d691240e443c06444203511000280b0504040c002c0d40802800200c2c0780e110542001890001d60000400d00d464044c40c9060b0035003502019144440c00034005000070071186800d030300010f0b081104844003007041ca4603200030440c0c2000940c016142c00f03400c2c00807490410000d226680c03038002544020361a145030104084d00910640c4401403502c2d070507401c0038003915490803d00c102c090743e050003407242c1001204d40070fa41d0b10003801403c2d5694a0500c60111201d104800c6800c1d5401030fa25150030140343ca90341000900380742d039a1440c0b0700d032038200c031148000c040d000401365020b43c020455140c3d44503100c0d03182141c000801050040344100401d0024040c40c1050360300c10185481141d544414180740388001d840d402e14018001d12031850000160ba0842d0000b0101c260380c50111041c1036103041f8010a490344240a0440d402c1d40800140002205500850b4486029003001441c00250007c88080d030b40c44058250b001030b6022500c111700c0001401c010350481c405100090 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 157750062 1250 157748812 157748819
    0x501060516020d060203070810090501030515070c0b09160b0c070e07021f0207030807031b0806010c020a08011a100206220203190203120705070b1e04180c0801 70
    0x148184905041d00d0159542604203034119511030020825095110009540364103092101401010301640e00701c0c0303d1401d019010442c0300051141074102c1b1b80040003460f0490b1f41b401c41c47e155400142c04181041003004062000c141040e00c0c460042c00c9090091a82111000c50000250400c0c1c200f40130b40d060811905150b007000207681e01c02d6400d602d041c1411b60311602e00a92808051007145400504500301c06400c0c0b50b0540d02a01110f8001d454201d159640d03000d04070304880040490450704103d0072004c9090501c140d8605034004410304042075000125000500034a12a134429802030b03460380580500306078805480b48981100303544100e40c80052080c081c2d01c40e28018490340955401c5015609081043c0744000006a0003a0071360b442c0041051007401e54031082c1c42c007a4068400d003051034521000400031100c240e034000001c0c02030582490107094095001d400182d00300800c8400c00f0076602d001030000c1000f480050010003884843e0b030f005c9002d0b51822007034907007440041e00041 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 157751312 1250 157750062 157750067
    0x30706080408130e0a09050d08061f3e031306050d0609090b06040c1103180d05072303010c0f05031008030c072907140106030f0c03060f050106 63
    0x2580080d4071104403070303c401c054011012625600e900011070304100100384503005000e503103c11a00d034019000d840e00940f00907815640414261641d5801010290120b40e4103040340c5800a100f001900e0004e908061034000c160480a0000028151903080901c90981d02c524285a1200c078103100c001d942019007000180c0000f10440c0700b40c0702030000000740e04643c082907034404005820441020091500f035800c04160b80701044584600440c981100d00364114028803440000300030a1005604d01407504010b10040426194420742200803400c035600061828031200010304002d4204070300c2c82c444411401e403980e1800200314000e0f4034040040c15107581c000c0c41c3c44007004660600341c0c4d8a442e40c0310b448981050640c0101c4090201041d46d11503004045070300300440c1c004000541e00c2400a494401c00d00013404400d0382e41007810000704c2c0026507030340311213000301901c2000056503551340e440f00d16030041c0c130b100100e4440c6103581040c070030412603224095245240c40800c100765030519101 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 157752562 1250 157751312 157751327
    0x30507020d170301030b071106101206140c03060a090b060304030807050d0e060901060902120109050709120507051c020108070e040609110c0705061e2107020f0c030706 74
    0xc0d004600c1000c190080c00191100081c82030716028082e43e03250795a0502054140303054440d6400141804801e000021002071018001c00000c224001d8052a11304010b508040c004802c80c1c100c0c2d22244402207981811801601c91045005034641e40c1c80c1242c10000c220708103820a50001c1c0c0351008036040350b202c0405495015034142031032500e41c2c4078060280d582d40074041c03c00e403880381412540451200080750a5000340c552500a0083d0b5842c1c2c29030fa0140d00400c24054140c8031804010411110650019a00241d490600118240d00c45c0d040c2c400c900d03402d40b02075641c0d03031218004000c00d052100301c110004010300c030f400007031491681c002005804061b20040070040200e02c400c189585644c0008003c1001c030004014074400791090b000749800c60745401c40a030007211000101814941c0071101020001013101c42001803031001210680c0101082c00e14181c0424a00d140800601140354060100340c4c00a1200c2e500394411030380740404003410b560281e00481030410034560011031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 157753812 1250 157752562 157752577
    0x306050d17180d06090309120b04110a050a0b0430060c0509100918050c0a0f05071401020d0e01020c030d110c06070903200618010c05030307030f0b0307030305 70
    0x2552660703584119561510160900700b02580800100c0841007000302660000320390511a4849150541e07540c1030708100500f0260b00544402000400100041c04060b50271100f00d07401421158404e40b40c102080010000350044005104001400e007d040c0c0740407499031042c1042030010303442c45180d01084044c24003e0800900080c1c41e418940040c0d0f014405480454001a09000281d1502c4200070240c90192107004441010300714803507c480d201e40252403060304443c40351842e01402c07481c1152580e22030f251850130050203000507000034110741d000f100100d0f1901c00250300c5015086441c0e0441d242d00400b41c1807a0301c1003054018a25010003501c0715010800d000207400d03410202200014032130340085060f1030240104000c00ca41c0c0024143d070070380707001da034100760380044056490000400030000603034000020712070f5000c580c900d900c0c030003445441032500043d25444c40d51050f01e143c00c01d4a404020a840e40c00051150003180708031401c281e0120300405080740f66840c05460f500c290071 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 157755062 1250 157753812 157753853
    0x6060312091c08160201110c0d020d0302030403061401092a03090809120303070816090e0a09140d020c041a09041a01240216260102030c0a0306050d 65
    0x2c08040080501d161503107055030051038150b03441080700340000407205454400c9000c04e0007080401841540010078001415000d040d0b510481030341c0c0c00300b10070702d601804101d0840c8010040840028081d005074911a0262014071002d035050500c020265045d07949440007114030784001444d90980000804000c92160030005001c0c1424104000107100c0c886420390800c92007020350b0b4441d20000f0095100d03d105580b4010203450728411702110302803801c040f00008880700e80038041000d284004541114403114001061049550b50311003031010040c7c0c2c02c4040e006001802112901400380a40901007103d04200e005041280c81a071380d045001c0e80c0c0e01604181c4000740402025017014000c544114500010a6075181e81d4051039250704598510080b040c01c1c0d006400da4000503050100814400c1041d0a0700d04004560075040300d0050464180c1c406594a20201182840114040d051100c101170781d904043c40d0107400e889080e4416030140444500c0080440c02661407c410345044e007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 157756312 1250 157755062 157755079
    0xb060309060106080a1107080301030303110301080a11120a0b06030c010903031e032013050603011202010f0203090a0b031e0c03011413050114130e030904020c011d06090606031209 79
    0x601000082502c20b00315850000d0004145003071100c23040c00b45040300d1107560144a81a10b4440011450100388505017072640600b0301200010040b5550400012000c1c2071031403a0007901d200f882c503200070098290340388000035042c04007500f000c0c0a001c01da00700a0030164521032455800420b036100360440000d0030b200034800400c0c594425080760710b60003a20340c1035104220600c002090f40754018010081d40f110340030f100050728200081520304903102c0c6800710031658030f20380054401c0d1070148901d50860104100f1902c596903071070078072409415140916502c030700e041c0b5590740d20301100240110308031010030b00b0000c5020310101241d064405103000140d91800c1c80002c2520070ba211035480c2c80081c101400818550010b0400c26982c0710202e91360b06400810410003001c59107294512001900104034440c110304041c2c0040803181050750000868181e0700c0c00d0b810f9580055514540c054000c0400d020115000b0040681c000104501403e410703141030140c0000ca104094681d401403e92 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 157757562 1250 157756312 157756321
    0xc0609131e0c020609070906150503100e0c0a1403010e01030210120c1e0c0210031d010504030201090b090105190507031508030c010e030301050a172505040b06030906010608 76
    0x158401c0c031400e45807441e0a00c00e0b038030206406134840313a00700c45410702d51040c0c440000d4900c0141c01407000311407501c01c01c11040c80c0240c1084070907030b00080c040300c000c14020030001203090602141520490001c080262600700342070005040c8a030000d0075680e00c6006000500c4110001a0340a04495040b9800004d01d611301030141c408004001003680e15502d8100c000d002076801c40410b02400d0110611400c650701500ca0641c1c4040180c04041d401aa252007413201d0f1038001c2c0d101c862145501041e11800d010388032900307800d40d40c040f10104e0060b51161040c00410130002c00351a00320380700070700a00507440c0034080c5060242d0203a80380840743e84c480d03002ca0010340c020340c0100f410043c590a00440d440c0c550303410a0b13881d40a162110b280e07610302024456100d0020050741d040c2d90004203000a0310340780101c004280c0d90100340101c2c0d0380c02019500d8010009010300aa03400350f0308005a21850315010030001150712081481d401510b003001001581e031000b150f0903054810700e040103000c580341c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 157758812 1250 157757562 157757591
    0x30c040b0319060510080307030206070f090e2d0c0a0302030717040b040512090604030204111201031b061d121e1605010302040305030403060c0c150c020c060913 71
    0x404640d800681d0b9520b90000e000c1c003155402941c442d42c2030300d5202e628103030340d04041950b034400d014010700181c00041c0812a401c0c480c0c0c035205205101d03840d003400d0058840e2100c00c00c035070302902d40f04025206600c11901300364211752144804005200220401d24000c41e00500074850301d8910020183d00100041602e0700907150340d92220408c64180ea141c0c900791405140e00c0740240c40585991060710174044002039040c1c11604922005002da41c00c2c10b266a0a010151002c0407801c100a0704c00e1003a004202c0305000c4450085001d0383c46100344442c3c18501910b241c182d42c01038010000b03030070792060b665580140d01101a04060307d070031405803280e250781818400201480708011003500840852160001001d030401c102000e10070031172035030701e80c0150101e215074400100f507500240400c10205030b00358480801e0821508003c246001c0076600ca0842500c02c1c10302241c51541c0e451b0303180400354104509082d01c8410390b021482c2180701000a1049250400704020762501c510b203203043c152 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 157760062 1250 157758812 157758823
    0xc030f030e0108180c0904081e0310080c0f1306090516020705030a0210050307050f0a0f122a02010f020f0417030f0a0807051b0c1c02030c040b03 64
    0x1508010021204015440c0050280141e252014005008640880d02c00c4a0400f82900a10004002040b104504d00c0902101c4900200306541c08079040c48408505814803104009004000034407035039078980008014039014032074225084d540c0c80307064440c0032500c903001c1020070104215410001040c7d4102c0c403030007810300342d00074682490503d414842028118110544d240e08070707400355809d00303032150309040d174400542401951041c0410700810318640140c000b1b5820068600d09a40b03031600003e28010780c0d81c001416600021906c00e40814110350081804644080c03041303040c480803898207135601d520103a400d504042c0d40714241d00f20310018001d6000200003a00044150f46500c4e61200104540d0428814051408004104102d4040d0088112640301039800200d504005060004135400100241840288031007044508026410000d080301548a5100241041c543c0042032207114910404130462420740c4280110050b40c0111f00400c10500958000484540a10003c2d1400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 157761312 1250 157760062 157760069
    0x228030603030e04090f020a060906090e04050705060715140402120118110d0b04061a0a080d0e0f1210110a050d05090a080c010207020a2403050403020715030614061201030803040c 79
    0x230741000001070080e820030741c0301048512503200e804040c1c2d034940354024803100131075004210b9001500c1c107119602d0203070050031085d405500003410510300c0c16044021200b4901c0d101c5403519001e01000300f186444c44410f0001085d0714000c0c880030a1603c00ca0003030500700040280304c50b0120090741d0a548408403000c41c0786411110050381414213041690003024032118a0741015051420808103003040d11040b011900c0b03a0b8001e040c010b0103000d04685065071000d8082c0c1c40669501001087e60796500da20b80307100580c41c007410100107031b00007610441d108000002c3e041203003400702c07007012a0000182c0b041060f040701c0200740b583c6c4290f2032600301030440d580140b8101c004600b04150810560103051202d10940709148040e80f00c00d4a000c0e121000150086401c4881d100134005610982020ba080351090048504080e1119102110101614021b0002a075916000c01c00c142c84e4210790b034464031007922158039005049095120181c0d0502000c0c24548001001c101009140700b0400002c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 157762562 1250 157761312 157761319
    0x108010b060c060f090f120c010e01020301030f0b04080f310605040303030f020d020c0a0302150f04020d060f020a0e09011703190507020a030b010504050f0603060610120228030603030e04090f02 85
    0x4603402444441f22604622000c1d0310325071030001009030110b8148200c80c141c0c2d0b0014081e091101032aa070b200040f0380010002c4451810612070884581c0c4908050044030310b04104075002451402c2b40c90704e03c3c4180e403c40700256807907044104941c03074001080b503094079054a0045840c180f01c2e484030019100d012501c030803451001a290040c10004a40151036601c60b5095440c4000d20f251451152101036820040034880d107404100113141002000d07900703a1160700045001203841c81e242c403c0741c00c01c0a10340c020034030070f5010204038500035000502418102c40c0c8080a601d074001140da40e4040c3d1100c1c0e00c401b00407002030030398847c099026a44541ea00503e50740f08180c4900d0700d507080100038460b00d0700441c148008140d01c28002042584501b0015005000c140e645d141002002d9001d95488010b01408000d038503a0b21903240024640f6503948500440003201c6080d141c007050020140c400105483c0c0501800001d84c04442614200c0040f980030946a609092940108040e43c0c0003c1d030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 157763812 1250 157762562 157762573
    0xa0f170703020d0c051e100e0301141014060309030a0503040f080a03021b03190509040f050a0204140607120305070519020708161410030b0a0b030108010b060c060f090f 74
    0x300f0001c07003203030029507070151280900010402c1d540344140034250b01055000341d1402055130741f18402c510300500c2244c01400440c4072030140c162094116030640300d250003924400f10034440003c600110000d11101079460380e15600e4554881ca4490066150300c008101c000004034082c00b9101c424004000d0b04000c560703907940720f80c44024000f903018a812500816542d25601201c590100c203907015410035003100c405000078184212990703805220216401659600c1200b10b1101d18070404d41300f66044180140d5450a2850f400e00456400c230b2441d02c03645040140400007036032100e61034001d241505000c600c940b610502600c40340114503c2039149001e05030140c40c20f0358005aa2011100c2c0c400039100c8100089958101c01c0c0d01e03600600c1304000310120080e100341800400d81d1401c100e2482c1c00990400900001104104154040c00c40400c0120040c804042c080c402d00d049d942c1c0440c1e98901c0c2100200019484840003090403046200c50400644030503418044050140340750401d440 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 157765062 1250 157763812 157763839
    0x60506040b0702030709051510050c0703030e12030406050417030d02031f060f0f0e030a0206040b0301090f0b10050a0e0306090106081002030108031204030311130509060a0f17070302 80
    0x400342d040400180e11134456a400080c1c1001e842c8500d6004003c2c2100114103150440706102e554190f00c040e41d410004c041003800c0c0045001d2142d1006076100380d60b080c1e1001e0303000b410172007082c1c55645500d1080d00100801c0205c60340080480301154880c4c01b8840300c04010101b15400c5008032616000014000800c200204018298164521011100c4660080d4032150201d900640a00ca1000071a903040002c0b44240d0003100cdc00d56900600800700c6400b075010b640800d0035900603622035500b0f001c0c0440113002400060203000c0e040c070302d84941008814000c00001c0c125860a005040601000080c1080c0c0da906c501c07804450000060111040c0b0b04003034058034024186881845840e01803042c00460390400c078000c0707904a4000800840c186808003031442d0810102800450606940381482190401d0140180014090080d050036100f07182005105801ca0700506141c42908040002d0080c0c9040081b2401a580c144801000300406541c0d10307071800d03440380c01c06913000c20f0068030007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 157766312 1250 157765062 157765079
    0x2070507030b04020907090312030b0f0a090c020f06060604050f06070c0816050103141609080d02010204143705031207061803020d0c020a03060c02010c030c02031611030106050604 79
    0x4600a504c291018105a528001c04176801803032800000c095462030034907148458480d4010314401d0000030181c0003041c01201c00501040c4c20b0b035100042c0691036a00300c802064052117259100f00b031680c00342c000c51130305d440010101d1207540180c0e40f26a40740f4009003c03a441c2d010596504681c4140345200c21500c5001c000d41e00c1c04200c41020008000e580302061070751081c000c0d03940ba1142c40c00e0701e240c00c0c0c41e41c081b43e0141c2c1c0b514001c043c040110340c0b0b10020301d02c00100f01740c689180e56034000594036801d103080035aa54540c5204036000d00c110358000c02c00c2052054a14081607801a900903107840c10003c0c1e008005440d81c8155814850381443c1a0003004c040014204684980c00410541801009240c2040c6907104080c001d60008060064a2030003841c66990303440c030003030502c1e2000c0d44035030356403044038204440080141e66440e0000271458051140c0060340800e80025400d00e000d000c8815600e400d0f038100240f03e03000381054182561002d40221001d0080100815100c1c1c0c2c54a030700 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 157767562 1250 157766312 157766333
    0x6040303091a190f1e050603030f0a120b060a021b0a080703060e0d0c02030a111801090504021008150d0c0801090b04110604151d040c0c0318050603040f05010207050703 74
    0x6554030980340903007136018040300d031181418080e140726407000e8542201d1107460040c030000f824030350140070401000b42c681003040000c129030074250b200c07002c00c444d03c0842c0000f11180210741a0003500300f0441011166000a2079100c088200000c401c05c103501400130030402d20302d6612a46080c0300301e070f0002c0100300641c2c101d0024202204c0031100704c0e00b080b00c402c071603503041d0b080080d4058000c5640e444c08904982441e108440000c1c080423420b004800b12401846400d0380613202d9980d950f0144021843e02c10200ca1030040c0ca03123442d6609003020743d00440c071443c00c045400d210300103070680720041021140348400282489070080118080310f05051210070411102150318684940c2e10304103d10300801564151403c81c070005024559001c01907404500321402d40081030310180a24030565143d004280304071030a55203058030440146400f601c0d8020a0f1200303508075180c00020b00c06a00c690041d29413082d08580328000c4501e2605042e030080c03040200292450213001c50210038403110460 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 157768812 1250 157767562 157767601
    0x51503030a0f120b0607080c0c0a03080d0e0d0815150a081009060b0a0503042307060f030603020d020919020c030306120a051e010608010608010e0d0f0206040303091a 73
    0x50310300d4072010f04000241191400c1e0071840d8080000c3c4007540100300b00034080d201107130021003190b008581003000100405070030340c0102d442c1c007000220b111090a0034084c41006035500340c0202038621200c400078002450013000c1c2e40c00c441c3c0d801c8044406580380d0107100c1e0300e8000c42030380aa40c0c4640f46070003004488129680c284200402c1c00004283d10188034000c1194080701d503450801c0c0054500300d60740e602c060b2050381c0d80d210034511149041c14000b005c1c1c00c803001d48401043c080b81f4086005c0d209072840085076041c140341c05000c0025840d409980c041f019411a010a0260f46282d8591000980d85502c446141e1011540c00d40d1580000010b500615044480c1c3e0b640c07070030290500759110320b0850010482d401c05002800c40562415014585c022110000b140c0141c50300c03c01800c4540903886403110380e46841d4201902c090a01810410b00414034050b1829200795a0182d902c07000900002d0406d80d8a080e01824031003000710700d0006103014040e000703580c00c103d0207100c1020100304 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 157770062 1250 157768812 157768817
    0x20f03120f07021f05040311041b02010b01030c052805070c080a0b0a0603120e03010f140f06040e03191704030c12020609071e09050c030f0f07050d051503030a0f 71
    0xc040360114000c6884a6094130011385d120380c030701411036603403070740d10001403000c60b81054403050340200d20101d082c0c0c1140c01c00c6142c0d0002480b00c10600005068035501d29050b000c1c41810000520350040d4404101c0d20882640c5200b1813031a8116421a5584520a4060002011070002003811140403800c60b00076401880315811a0322000b00200448005200080040f948140100c46071809542132822040f0000c0c00011410011040841a624408124030404052204116003000364510385a048001540e041006006c0908103660b07900c644103480c0300f2518009031440c6404d2048400c030450310074085545945040c03514001d483c030442d03002c04031000309100c2c008020312440016182c1c072a4407500700030594986000040208080407800040e060203494402051032411030041a000340d0211240c1c565900d032107640382c40741c0d0101810510090038070303c00344402030b940a03054403100514400000749a4540d10030401c40b0000300707045a5010b003c00300e000560560044600f003416081034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 157771312 1250 157770062 157770079
    0x221090303070915050a1d190609090207050d080a15030309060f030506011b050a08181203070308010501050906130312230703030e030c01060f03030e060702010c020f03120f0702 78
    0x8454241c4d2001c6006040b4001800511044e0a41482054200c0858204140300d42c1e103071222a0119030810a003407480c1042c1d01145000f001510350180c0c070b40c0c008000300c0004604100c82c503640d80b40c6580300d04034a002001440c1010030b41c030a11552180c000b0301002c040c1c442c80c3c140e4034500540402d046100d2500801c40c10f070f0003421001e0003801414403884c1c0580d40c0c80e6001110404a002c0004469001d541d03500c610581e1000140690004140c14a1a14544e0301c4480c0340004010305034140b0030003e94140c1041c000040080e8019107941c0c1520304c00d00301280c55000c0790b0302003046405000f9141030807031b950780c8002082c00003400030142024111f03a0f40c13034505802c1c030b0380340e80d001003010b140741d01c2d0b41008111600109200754080b1500650146c10b40b8034040f01c281c101403d40f600d42d00070001152400e5000c10030580c02c1a405202d000c82640c201c0c2c205140e940020b080010780d503030003900902620300c4070a002e0b6010300a44d4045c000d81b4070b899854121001140c10150001e83d0200d0146401 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 157772562 1250 157771312 157771319
    0x204060201050a0513051231051002160b030402040e0105040f06050c0918070908120c100b0f15040f140a0b090d080903010902090f070e040203010b0d02210903030709 73
    0x600e00c440212a411200401c1d0300c2844c1d40d007054056129541e2324003003c9909110320820041c0301001d07401900a00d51100c10682040c00300b11071503614401c210103550004800d034050525a11411044401c1551400c1d103d5943d400401c0160480484400d8071754603060810080010050301020301d1401140d0411050780c5083c0380b010f0520038915041da03c400c0e1001e1b03065900422904080c2e21540c2880d20035040c075550207015203030014503a251121000c01198440c903642040090001003185080180844000a0013040501401d1a0300601400054070b8102d070300c1480000310390003011681c050b544419034405c0d4176034411208800781d0348120395171b00c000030f91340490303000750361302107500400b1800b2011300c940c1c40c12290b5000460300380d01552a04001005655589513251080703100070032a205929000e100100b00b1215402d03c944241d2051005000c40303082c00040c0c07200c040c480d0300b00507039800200300d042e0803050341c0301c4200700b45046000400076143c9002c0003850142160341c4800c0702c407a46 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 157773812 1250 157772562 157772581
    0x3050f061207051512090d030b19030809030a1401150e07080c1c050a020307180e0c131203110f0c060f280e1008010b040b030601020f010204060201050a05 68
    0x802036585005a02a0b50180194a840c000550381e203020b050702e0510b8107145110303004940604655401d007a4000300f00c0d2200c8903806000701240f41a04489aa041d0380c8080b00380c8515005e1800040e000350400f18010500e5102000000d0180d60031400104156100084490180c24540858442410100000100c030341d50030340c1c04da0256010352202036040d651507402d03000c143c111001120f41d0781c1c03030302110084000c175600c10580110884200581d49262a900140c54042d0741c40d044480c40070014010440c0214005059402100f203509442e5980d11140c0401e1b0802c0f043d030003160302c00c18404040c1d030406821001083d80881c0303c03400d883c0900310042081740c4070001d4a4038a9080b100c100b00207004010310740300800320340070452494818910b43c80010380641100c02c5a9602240c180b40b91070805160662105042000e0740c90445015810030780050702c580600c0c404c090300c03c14040046181a0300074066103444020340700085499664581c4028080e1009541c80c07412039140c030001c100e035080f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 157775062 1250 157773812 157773829
    0x103020d06030506011703072105190c03031d0601090c05040e15040c0203040806070e1f0309110f01051801170f07120507050702010809030f0d090203060106080907060f0212070303050f06 82
    0x20340103655100d200c02074180c0300c9c6100c0c0c44002d880041223400c00050b0001e44040d003121451956594800001c2113162601404840d03c1e0550200800005403258076104800110581920010240481c400321000c000740c81600a68000c1c040e51100d01c4200f00caa0100e503a0905c07041c90003140d01384180303040600180e03100e21507801020400e40041c8005250a0f00500740f070b15040002600603024400d50a049503258101c660405c1e001948404881c0140050201c81130710b0b42c0e80031581c0c445600203500001c0e00c1c0e403084031980d10f030205030442c84140c0c0713a005000888000c0704000540c1100c1c90242410017000d10301b110700d000401c061107100b09030b0905610606100d041c4030703103c0714a005029001540c54007001003ca0070035200c100b01c4106003042c03540241c0f641c2e0454400209001034981304040c00d0440580200c0c0030440e900d000c10440410004039141103603140c2c01e260032844548801207081009041c6030050b11100006c1d05810194590b01c0240b141d40504205005074845030304122004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 157776312 1250 157775062 157775077
    0x608010207110118031407031208090c0618090402030109060e030c06070e0a0b070c0b0406020312090a0b130c0306051302010e0a08030d0c0c0203071508010909020d0305090103020d06030506011703 86
    0x1190003003083c000036800000c1401451425402c403801f03a41d0f00d58031042082c103501400b500103410360062042c4840e041100401d9410704846031030404540d1407c181203840340c1b81000340700da224100414150748003036008400e655004a07091089011803c41c199a03a48050b00d4a03804c0d10800000a503507034840c81d8144103481004204500c410701e0100c042c0017982180307005540c81c0c0d80d1f6050000d0003805010050000b407000d90080e58882501c0d03e410034002400030314881464108003190800140c0450382e0660110300c405d44c014003041d1034140012410856007009008500c0d0005102904901100340d9200701d01c01d0b40c079aa80c0e41540b1081c041c41e60010710403100141d0040c0100440c0c1c0d07100d50010b604411503450007050b43d41141c0c0000c3d1506030b9552000d98141d1140154144455100710340b1805049070720001d00c1414681da0208058004501019082080c0840c1000440e8880d404580c2c2c00790030340f2420720a4a1722401c0c019101d040a204800c02000490481d4028003004000d03a8083d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 157777562 1250 157776312 157776347
    0x60302090726090304060809010e011d0f0615060c100f06050f061e0306011103070b090d0801030305040e06060702090915071817070308030115020d11031e040906080102071101 77
    0x20185481807d5400c0400075201a403203540b02c240402504009101d03e66214444110025000b015030403100d0904071004038102550304080201b07c01500f82d20034100c03643c04241e03001d6a588449418040c2468100800c105040e03003013540d043c010344290b42194044c0e400444280005c950b50f1804c02c015486103c007001d50f2049461006224610010040d592201041c18511406015911032034295070144a0880b80d4088020a00150402c1003090340610b180904002d5034650640d100074000d070046200d0a0f5054580d0700c009421501d441090700c400c164044c4c940c24032404e190700400d0300e030105090442d50146450001a010a101e2600d6001c2c1c1d030001560041c1403030808030354910640100d10221101d00c112a000000140d00400a500070074101100c0005548255002410460141090010441c544c40314409403100030040342d0340110185c601c0030700d001c3c045800e01c60364022076000d0350800c0d16100001602002c10b40050000d035100c3c24900c069414602e006494030540265001017 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 157778812 1250 157777562 157777567
    0x240503100209030a030305060406050402040801020d0f11030133020319030605061804020702150307140f0a050309010b040e01140618180a020a270507020d0c060603020907260903 78
    0x200f4040e5100e0740e082328010300045880ca45440109041e0303480741e17225407016940002d11030013400203071098800d00a40ba95040c03040da082c140301d11509000c1801180f9500b20f901c5c20007441401d03080450964002240340d00384d12008204004ce480b50001d101c0c1c000c07102c0c0c442c0082c1c94954400c3c40b41506540c0c0c01801d1504024a100c0000514450203c8080e0007550800104003d80d96136840c000748801a60b86007a44d92808841c0200b15880055a9120382c1005202240030300e80c2890a40751105803904d003807901c0b0350300c989000340035005c03060101e90002e00e0000701c0081908103401c0a60711200c01038111401e91650700078055003903041d440100300451002d0109011442514005c0580515981100d000c8210303600050810300382e0382d2280c50300192424600310789004628401490100d0300c41c0801052900e02c10182d11995101030000030041d01c0b4100b0410080294881c601840e00600110110700d8498400303001c50740300b1a10500b00c0140021000d103105d43d081141840385103100003a50 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 157780062 1250 157778812 157778833
    0x30f210c020f060c030105100e13091b032604030c05040203060102031c05100602030909010e0702072d080d0c06020901120f09110105280324050310020903 68
    0x40200600085801140a06140c602e100d142c1003200d14041c904c1c02d424150742e549030004109400142c0381c10383e0b042c040b04400ca903060382c0d41c05020030345004500780d001c01c41d40d0040c580241901004204111140b0501c0340105c00d000407400602c4c610203840c50104201c00030403500303510500640c4001898812003540038803c0342001e401858118a041c0122424500314402c000c814100302c28500d042d040c0c0e030710204000c262005a038140200721714005545060783c0c40001c01d604620502034110564252008240114800c00c0030781e0003050003415000703407116a0031140d9240640c40300381400c08181d000c4041200400401c44d42c400c010b040c0c41e560255038969031480c0c0650421030440d414032001d000f00394880f41e030a0165495071102c05a000416000510305800d40d10046910b440c100078090003447c103080b42002c002041d01015000d20071411007500300803030152110222082002a2500300e0280301c8068040060a58404a055030701d0003541c0880e4000300c1c02030096180c5d2503400103a184 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 157781312 1250 157780062 157780127
    0xb030a06021321030905010c1a19150305010506090105100f02011107261801051602030a0b0103120f09050103091b0602100e010204050d1e061404030f 66
    0x2084100c084140b503081055440315820a5028540300d1048503000800303a900415900c40322500292900b401c00e445c560003592542031741d440b2140d00307185909140c0004264000700301c40c4010310044419200f030112034421503ea24545c02c1c0c034441182c10b0360800011601501d40038030342c031341031b01c1020341840c5103800c9003071088512685400d003910640d56078a81850104005000074840e16000c2d600e0b41041d120010300c00300c13070090040b101c520801c1c001c2c000c07100c0007000381c2c114419150003407802c41d840e0714400b0b4911203900c040e50790003541032081d0000c0c6800c020402024504880c0103c41845024a04210556224005003400e03000148190b1003400658001c2d132003c0042400b903076190440082108185000100c80e800004c0036074445203c42071460024050400d5011800c1b00a6007401e240a001c02c2e5407880100c00100440064041d98442480040741d5070b1059030045001c1c4540c0d200e10794040702c0407000f5607045e0b000075461031941092502695503c1042840c1c460f407029500783c0f01a41 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 157782562 1250 157781312 157781317
    0x3090501051f23091f0b0c150402010516020a09090f1403030402030d0309140d03060906050a080d0c030c050a0602070b0c070b0705030c040b030a06050301060602060c040902030c09060a020c010f030b030a0602 91
    0x88100703150345c18450480c508021003215016024407030703d40c2d540314074a4441a140c45d96011881c00180400ca0030407005076803000548000108480082ca00030b817140c40007030b206200710780061820504d060141014440280c541c0001c40c0c0c011102130f01c5990350100384a841c1c0c40200d8020390160b100c1550301c0d01c00c1d071090340104204e40c01051000450344d18a40d00b1410981a00e0120f00001d81b10074003840a031a0a114902c01000200c1e1001780c1145012a440c2e00d50030710200400c03d00a800480505040c00ba904810145601100780d07010001c051a00c0002034000607800c1d80c0c3c50440700c0c000b8850342c20040869030030760740103030194809958200c5c0407245030780010f1448192800038040010310f01c40c1c2e603000e14080e24500c0742c0410304500780001e05086841c242d0000e41158445414014031170421000c40d81521040fa02c096078a035610311004065201d00039081e07410000014042c600c240d80441d8440c0810707400d0741c0c1e410b1040811002142510032090b41550303d070300720f044614001401d5600 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 157783812 1250 157782562 157782571
    0x7020a0f0f0602190e04060f0f0b0901030608030a0305150409050a06050619080a0b0c03040b1303030b090109020306210c2107081501081203010506070303090501051f2309 75
    0x1c00740c0307090642c114000d0b01c0000072113a440482d04070040e0f400c86140c14040d0b8809094600350704800607280a58604c5100550302c1a00c501040010b0907007030f180d10035003040f40600004401c803565010701d414002d00401007140e44401403807800c00102e0052502c1e00812030201c4d04a030007030520048544400000f450098007240c3d100e1942005851012a007004203801005604080c0c83c061030a0300703100c240d424009281d4500803100304104000544800f1041d034103c1008903451340094090300e0160b00410040c4401580704218000008038807903144c00071840341100742e80d00c0c82c00002c0ba08106240039078a220380c02641c3c004454001f06401c15160010203503014510070510041819a91820517540d600494815000302c044103c5404d50008290b0040040e9002400100c4c0265020380d141d0106010310740c822800000c0340d00034075119401008849401c01e008025030308254071903030300b21076811003036100d031078135901002078a280c45500e0110010f40701507001c140e4004480c208806c600c03000b0b0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 157785062 1250 157783812 157783823
    0x912091e1d070c02090a090605180a030f090b130501030c0c050316080f07030c14060105030c0d260a03200d150306020705031c05191d0a1a07020a0f0f 66
    0x100541d000d071799070442c0301d4000d0044400c0000d2484040c02c002058820080c084260104c0340d02241d1440300c40040c1041380d060b0140380c0a40c450055110842c0c0c81409030b4040070580002145210f0700f4140950f09400700c89098808116010300420309445080000502400d59001402000a04030040316460300c40340c455540f10b89081d12035468070b40c2941000b0360540000d0305c2150480308200000c90181d6040035004020006903140c40700196642c00040003a0340100081038000080141c0c1009081e9100c40204042940840e680c0c444501600000c010728002402c10b09400103080c04019a40011918034100500d01001101000050280c625102c0840040d11400101052180c03000d002c0080c420790281d5650740c81d41c0c0090204440c10014105020f240000340f281100703503c04041585140c0e1480890f11203880700f00c590b8045ca035050305080380d0042c2d80c8003504100014407201101003481d444141e0646403030308200d0303030780780b42ca00004c0c804490101da2101140b1400c00b6641100d1040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 157786312 1250 157785062 157785077
    0xc18060103060504020d05010305070e040503030a091e0f030f05070b06040e0c0d050606041b08040f11210601080304050303180307031203051014060706050a0912091e1d07 75
    0xc0004c83c089900034000740000a50300c00041c410480c06000200003860501e00da07403847d0410703480e015181d2001400390060300755244000010052501d403604040d600031501c1510b012611300b84a940390400b91400c400081e0124411000d040c021015216229005019408190784040078040280018043c40c0c01c980f207651043c0e0515a138120000110b0380c810000350609003040400e02c41070b105040d040c0c908055648150b00026940f2a151590094000c400305a018000d03040140c0414110750760a80c00c200c040b000959168100440d6504281c620030464281d6a030307880880d85c49000c0c6020701179043d042000200e860315031116000c0b0141c0001400e03160301d20368a541d080c690741020f20b002000300fa00c4804004007580003c1040000340b00c940000100d00026400181061103103500050109680b00f000c51041e100315031001c0380303a643c010f210100008031040050051003691003001c41000a1000c012030407841100c0c030108480000d00c179070038601e04804406201d940300400c0c41041250300c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 157787562 1250 157786312 157786319
    0x5030c07061101051303080c1809090304170a1205310311040c050f07060b060403051501060306060c02010f02030d050411011206030206040509180109050607080105030c1806010306 79
    0x14803544000300129202c490941d260300c10a1800d544004140c905450075901d28280801e070403041c1c60394099568030882d0380c2d805c1c40724a0346005403144242d00e5001400c41c020070041c0400000104162582064164240d50300507100035a142030f00c1d100100040a500e9500300d0b101c0c05000a0400400756a2240d2030607661061034000700040d18004d4200d44482c17110400500c01403220f0b0316070401d0140d42c00e01c407502c03031294040c0c0180f083e0503283e078826030000303001c2e000d21081e5400011012030041606545a60342d04040d03580d22418403194289141a00001071003501070701c14030b001ca49031030300e9070001002250015500c44400300491020b50108208032604640300f489520710451051200d0940c11352020b000400c00e060004d05101d07070610300b44080c001759441006480407110125401e032541c0d0b9a02d00c0107100071208401d0029a5030900340d400042003c042038551150740c5569a1408586c0c1c0c4000f05540d81600700c6809402240e02c0c0f010002d42d80410401075400001030501003131481c0e4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 157788812 1250 157787562 157787587
    0x50f060405060306152b05070f0807020c0a0f0f080a1e0f0f26090d080a0201180602070203120406122c03040906050a0303050412020409080415030b010516020108040503 74
    0x10103001b002d00c404040a0180703002405412409180d07080c90100081e1910400c0035001c0c04074a0031120500c41d00c4000141414420880c1401906015190310f0944d130f9190450020050280100c051020801c0c8002c03410720b41c00034407007440030b40108a142481040e01d84440b00b0000015080c0c1e680005602c0c0c500110750780c0c403c0b10388801d00c20707041d08070600c0c0d6440720280c004140d4018100342030020800164031b99a005101805290070803c038951300c01400405900410407000c02c2400181700d40f405c0c17800e020050b80a0145035000b0341c181d40104514500c542003078452402403401052041a101031000314640c0001d125000500750418488d40e4100e0b0b8292406074008000e50940c400034091100b441c19004100c000c150540300310800038216500075106000d140155101c07100d40782c00501c1076540729040b0002643d000070b030150b500c0c1d40301d00c007016001034512216004a41403c0300c032203041d48131300b040b520784240311210021703058410781c01115040c50181041d9034520090221a1960b00d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 157790062 1250 157788812 157788817
    0xe0a0f1a01080c01120c09030b1905090601030c0518071101060305060c270d03050309070b0d020405010f02060c0d020f0d23070203030108031c020d0c0315050f06040506030615 77
    0x702c8200510704000032100060844060b10b40e0700780007900b800700b40d81e00305400c41d1034001603a0b4882d0740d900e46659030a0100c0084100c40c3c145149550800e0180250140c0200c0c80b24142c074081d02d0034250094842c0140300d415849444042c8014469100040c80d09200d1451000045d0b0403c00200740e083da00c0c2c0320706281c10400e5600541c0381600080745110a140c1d00c038034291031100030441c5c079003003c3c01c81c2c0040e032442e0500d0009002d0007400400503d42c41c01c18041200503002445407a07460746105555407000350130600070a0f0100d1100d4203101241030001450912800005000d00d182441e51300b06100a900103d021100c1400b0a200d0880c14a8070b41c0501519007840c8000c04102d00c071140807410101c0340281c0030f032095400420061012000210480301e9100c8104a082c1e0b40442824006000348600010b4854440c50904104901070781171704107041c45076006402c5000180c540040000e5071b00e600c42110b40c4654100003c01141c10300b50061a0301010050011074003a0800e14036960a0b07 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 157791312 1250 157790062 157790069
    0x2031902100e06010e0a02091206040309090c02010b0f04110706061202040612030212030627040b07021216020a030c08030309011112130c05042408010e0a0f1a01 71
    0x50308812100418900c003807150360b00c2c00744014000c140c5545403098840700307294042e0641900715000920310b02c0075180c0c80385400e80308054000b119075600d4a410b00420b0388282d802a00a154200304403490b10f5071050180645100b0014104a4100200800c000c010403410301000c00d44081070010a0108260b0320405004240c002d541d00c061107540e20400c000c4170016041010000c2100010307901103030780091016110740380130404642c0c1c1c0d1110b0780043d0b00e145030f02044014551144030510640c821400209014030f11a0000442030345864100360b8590020741801c1000d2402030051400c184281c0064102850010b402d540e0030644988414413003080c10f411410842e8400002e000c2d85682c2441004411150a401141490384490504901d6100a4a160398031000320404d40b00340150481e0703040081c10020301c200028600c811003034400b180424501ca144044028002500030700601624041000f8400601030401413581c0d42d40c059000b44030b059a030545504c0c80d4142c01c44040050306c1c040d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 157792562 1250 157791312 157791317
    0x110d05010615120606050c120c030714030a09060806030d0c06140403020a030801060305040b01090507140a11070506040f0308181801081605090a0c020a06060905040b0108060c0415020319 82
    0x700400c4940f010640350260b103c0c1080001c10401091400301c00701c0c044601d20000e03101580c0d11a0303822503891442c040c0d50000b03002d500800b000c8101402000008203840905915002c0c1ea040e40d4200903504a4007c5035000e030580c01c01e0304440c40e114443c520300d02845d07108410000c0c842c0c0301110190181c4004650031009a8000b8407920180b6800091050041100d0300d400d010754a0039588241c403030541031248410042c1c0703034030210368458002e0021400c401c0e08414003035142d40802c04010000310000c0c14041c5103003c2c0030404030752820329030300321000c1d00c01002403080d440d4039594400805501c010010805112100000745040ea030301e859110800d00180d50f511400c1d414090003508140020980950030060300c14100715030b44900d0309042e4044141d003c002640d1403843c10a84c248144c03800000c041d0f03440e1440c08251500c0a900c458020780c050040d00890380c2e2a0218a56203038020303580e100d03103a04280700801c0542400c000504584406205990816502e505441306044216406001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 157793812 1250 157792562 157792577
    0x121509030319020c19030c150f1103010b03040b04020109170607030e06091f110705070303112a0a0b0309010f0509070b040b0a050403052a0409110d05010615 69
    0x1954a0074a40c02c00c49820300c100f1807801001d0200b03240d9850b4800d0100c40f040180708040d4050500034052103e455400440c00341607042d111481b400144100440310000c640303000b400701c0355000190180c03030586000c0e4001c1c0345107880d2910b418940303e0000b88202e04220a011010904802003030841d96125418002800c150070685405800c0d0752180301307644a5075000303400708040503e001070074420b120310107100e1510200e10b45210342d02a001c000c1d1406034181001540f14100000040c1007002c4a0107940d50000750002d40384120b031212040865040340103c20f00c0641c64901c0349240c07200b08284010aa248a00d40c1c032610b00020390012a020410380e50342d0361200d81080003a008885c0d21a00c008041e004890a10403061890f014600a00c0100e000c0409e800102600030409c44025542100840b1003464400c1c801c1c004c8513100021188006c1c3c515104600181801d000b61104a984503800c1c0d800307182c01c44248411f24a0840c0d09843c03645d241c0d03800062062814416150605451351010f5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 157795062 1250 157793812 157793821
    0x92a042d0b01080a0506010f030507030b0409111005070305030c18040e012a0207090e0307020a03080a030f0204030804090b04111801021c08010b070501061a0913090804051215090303 80
    0x500e40300f4002c12195025040030100700707003aa403000d9006024850f6040010703131502c0703a40c0c0c224001d01c10941142d0300b25140050340000e0020380c89041200071400c480d840f07081e070803111003203983c1c0c003440c10001d01042c0e003400801e05c0d000d0a80040d00801c00000640c0c403009074000c0011f030a40305800c0981255940d5250303010b0180205010702d1807988480c1e160003622401000d0003d554a1551140881c1650382e60170400b44681c0074002c440841e5001032180789002c2c2c036030070540782c282d000d614100003003441c0c0b02c07103600544000d00071744003101e812440c46400c02d894244480081d001d41d0b00380310741c019a0341901220a0703440344d010748140085501000e5581c18a1000a440d201c0d4007078a880610704a441c000e04e0361984404c009065a414403502e0391210302c14901070340034181c103030442e540c80780805207803048480b08a0050424010211220413079044544500300440e4400000034003258410030040c00f850a09050112481c001c00003142e139031441d0b90752410400801600d403540290400014407 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 157796312 1250 157795062 157795067
    0x30103060b010e03031611030a0605070f0806030703080c01090c1401030605010315090e030f04030303050709060309030c020103020f0706021206030d0519080402060d020a08092a042d0b01 82
    0x7040348034081c2014a41010f858000039986d000f00720b4046080b2615919080803c0503140d06907000b21809000c50700f84083c40e203441c0001d03000442d6000c2c0000c15000e03500d50740910421020717000d020301401508140b800e41d16058084d81c49204203203a69904d40721804005410007080e030004007801200d1110008021000400741d0349150304c094100b5042c0700c0c0742e0f20305110b0101d420088854010300007484071481010307203080d4051400c81c0288511b0120f000800d15802d900031a102e2003041e912480159190703141035080741d64110024000402d0012800c0042d4020b40c010300040070304030700c00c505001ca03643e90b02c07043ea80301e007804c08403620300c1c8400e21041d42000c11114a02143d10708206050944141c0ba0f0703c4143c420000c2070b020041881f02041c00e40d21008100d483c020300c82c40003990380300340e1244048c104010a0f00d00d608070b441340720020840a02c0545990303096181c800d0f4206e201c658107004103c094a50100c0c4c9000312540b44520f0007100d60702c03800ca040c0b0040603070700c045070a81200c0c1c0007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 157797562 1250 157796312 157796321
    0x306060a0e1c06060b12060907020a050619050f09031c0f1109210a0b040609200a09060f05011404120b0f0a0b090c03100f0803040e010b0c03040513020904050a0203010306 75
    0xd0401181400848031805006c040180e1106043e2042c10f041c0d80d0701c0100b03d2030402d588001401d00d0280e001441204803200381140300c0d01c134000c00c0511040d10340c1c03a0031190b8841c04850348025900140041c41442607002c00035140b203011810045032074600d41407070f03d00b164098000303c900c60600003060320b01d0f4100058103032541c038104420410132001442c02d075911440c2075007005080100420000c0c1c10080b080c0d000c18035245e04890321103d00c0c01000c0715000500c2598160910810034154001088803140c003411064900c3e407145904480e181c02d0040d100c0d8100c100170842e5080d4144000702e023400088c41403a002c40d0103110f528220b41000407100351440d1016200c0030906050600740310b41038031070403082e80d0000c40d0600708071b40e00d50360722404420b2040d10b42c12802d060303000ca6a00088904000001d4815103450050300e04450f640c840c51582d4510503000307155441e810602c000c002e0351030405910b505465000c0300141c030301803103140001c08803281110310219160f4040700520a01056209 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 157798812 1250 157797562 157797569
    0xf1e2f07080309030c090c210a05060f010905100c060c020313060512070503131202010e0f07150e0303070611190c02012f01050c030421050306060a0e1c0606 69
    0x140d07150450744808a45c84aa104103000d00414882020405041581044a40c0071f1101e1b01c51007030700300d00702000203e080000e0307130707888070050401c3e01003443e62409a07068422110142c4565a90900e040b06111742440c00b0017514082c44104250321000c90105d0141550b241080d6001d1079a65810030a540822103050b00000308001c0305005040001c142490001d030000020304040751070f55107100c4244c1042d285000010300f43c2030b02052908503e03405420031144241140d0940304030f481c902c442035075103442d43d20800e480b500201c2490201540140410103508902600b40c0c1d140802e01d44540094911041c0600201c990000d2212441302c40c42c54003050001241c580b0350510340250700024130304800148582000c2c00b0001031600f050071480303040b007008014075000340300c40e1030071b0400880541c00072a0240c1d04491000c030303d510512002240081d0a4455448803411600c40300103128494106002c15424000702e10851099907444800903180c48020003130060300c0071203519091064891660 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 157800062 1250 157798812 157798829
    0x6040f06150b03011a0c1c091e14120d02160f1401110f01061e08010203162616090902032403010609140f01060f1e2f07 53
    0x20007440b211000c9003c03681110722401c21200c480001400c890041d00c0364903c40d807114445d8044401481c1c1584022841d9540030382c481c1e00a0640c1d0300c1c0c0300740a0340340c2e8184c9a4000002c009081c030401d0005c1c96182c8001c400508001c0785011481152071030aa01c511242c0c02603070020b1914811940c610750b1240152101c0540040003910b0308000320380300161041d545040c4582e0ba80c194547c4001040740103c031007a010020301c56580e03a4211403410b846984044414400d03042c4c0d0209100c501402124020300b01500308200340580c1400441c0d04488403001c2d0000e1820380070211a81c52541001640909401c0c500709006100001c4d018242514641c0012139180c014010000d69030744526045003011003a02d000000c40110703000003801884941c01491480345001000e000c06008841040c0c440c0c200c4140004580c1d8a545080d2052560300c22040d0000d08001000c0fa01c03c84410240b01c0315400608001d404040200c00c50448002c0e10b10003407000f001590170a01405504010480050000d01c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 157801312 1250 157800062 157800101
    0x20c0a17040f12020105030412120203070324060e060a030212190507020106081b030f0102300906040f020607020d0602030a1a2107090504081908060904140109020306040f06 76
    0x80e130028143d800000d01c058a080800c25503401c020f4040c1c5119125003074292811550780c60403a001500400186044405002000601f240305802103c215401e0321403179102c1e00d04041c045006c010059220b181e0030004c1503000c0c0014100380d200e001d10303180503400b00d0b4a004403000302001100c04540b070003814501160704250b0100452500882c05211465080170002c0001d20000702280c540020030000d818030303601c0010300305090b803054142d44240304000e00006003805103100c00d0070b0b800c40d02510030030180e0300520701260001d5107000b0306042d058070240c05603080901d181c00069544440e0300301030340c4140d0000100641209a481900800305019001490841c1a1400308801e80d0b2180528001040404110b0501220400c245c000504191100707003c18901482e003500303170b40c10003030f1840090120850104810750040b85181c1c81901d0280240f1100c1d90f89840c0d9000700b41400341e07010f00d255030355540c0f1005030714144000d900c5603008141ea19207011507450000210b541d507012242007280b41 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 157802562 1250 157801312 157801349
    0x902090a0213090e0c0a080d0807021b01030f0902040e01090c29090301090c030302030408070b180f060c0a0f11010c02010c031d0901030b090f0c1003020c0a17040f 72
    0x1c9074500040d654100f0000510b10f454106252502601504d40303580010f40c0b00c03000400002c0040d0041c0080070541d41c84c06c0765101d4100982c8e980c80403082440c0e10480c8100805820b5110340d12080100400c00300102e000c2d2840d402090071910ba411405400340d460b40070142c18400c03003644000080904480520010401e0054124815104120207e102d007000512841542e4250040c0300c51503081020302c1009030341d038a00650340e40e0052140c501c0c1750007008000a100d542c1c51058a5120010201460100080c80d0410810700d1104d140d0a502c05024400268602c17401c200414030a4410004942200028242800900c110113040c1c0e042140c01e01001005176882214150101d60508152520307015a00c2090008982c2032166078201c01c801000100b80100a110240109682d400f514400020304901c140c45114006010342c0021a0711405e84640c1e01ca6030040081803481402e49040c8412682d8000d45440b4000d08862000d002150922080b903246004c1c0008140489141125000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 157803812 1250 157802562 157802587
    0x6010506160204020f130b03010e0603031201120f1e03030b04021306110304090c03051f03050706140c06010305030a020f01050708010905040204090209040606090c050c071e03150902090a02 83
    0x710000000d0040d500464401e90203250841039507100d20366404100065900c3e050508007640091003004080280c060108596003404012640030700702124038803403280e081c034100503e8000d018008481101c500c41d030440105908042201d80c8203040e440d0310900101a0134020280d80c3d40002d9144210320402c94101600d000d091070f902298090b003814051440c1c0c030102c0790300314020b550101480f54203100302c911900d9410b61005208500010500a0040540000d280a200317107000003405680011020310801d809103820122180320114010710300000b03079400c0d5041c01070a900071681c0e83d001040e400e0340c1c1e80d01840b0080d45101590002c00462804150040030840180b1814054030341c1d4030045410740d1143c0c0c000006a54000e05002d807a07081510306403005165500c6500c2440f454441c0700d0f42c0303452040046551099140d402000c1c0315082001c41400070308600d10b41c8203840c480e200000001082d05410808440400a00044140860040c4036a40d54000c0c08400f0291041203070121489 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 157805062 1250 157803812 157803847
    0x5130609050f0c190e060d0b070804210c03050f0705012f1206100504090203190507021b1002070509240f0303120a06090e06090d0f020601120503040f0b03070206010506 74
    0x5e010800c4642c060300c46030003081030f1240800340681100300107010002202c0c4c000030720a019178407443c0c1c02c01c6042c85c00e11981c0c0000d041d03188001c0000345401c0c000004681b0030b43c00303080c007031001c96021840e04100c1d0f81c07410308440040d4112940403004a00319894a6004262085200c4034007032030302c0c6803480b04295140403000040c81e062051181c00c440d061400e200701d0a45003e00000380c0c0841d60b90030600c1700003071081100c40112403c141080300041820b032021400076240b00d0300c401d41110300f052440c100030288040411010031485041d6000a95550f192006ca0152422022400c0a44201c0620b8007819500c2c2450b0ba000d5840040a115181c80000c02c484400c00362080c40c138110340702c1000c401e014000704d5211021060500d0b8810714070207000301c0c80d03a0081814004460207010f1100f015078002034211b408501503000742c00100044915070314803100992144c4d058901e401d440e5050341c42c51074425007210403140740c04000c000c1c54940400140f0301500b822a041410524018003644424 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 157806312 1250 157805062 157805069
    0x60603040224040e07110c040e03070201030b060c03041203020d08040b190b040203010803040f050406030c0302060705010204080a08070501200307140408010e0a03170103051005130609050f0c19 85
    0x1030b80c84041e00c140b078298000b980c01500d2203049150035405c0c00c05000380403100c1c5890b00d04642c06001040c4481d89420300c00e42c0342221411000d1030a10441e0b4006400910500048907004030b0208059112040248014005003400d0411000c1658440c10000e00e0154144c00760420712100c403092001154000f9031141d072140d4040350a1010320200300905018000400b01181c1050000c0000b082226020000d4070a840120a5001039155a201040140c90482c400030700b240c40113280500240c24003100911003180240b0015181940d50340941e4a807840d20502500c07190030110b5a00204202800307200c0050303a90143d00da1040c619104090558800505564184110512640742008809040c1c4000b0b00003040200000224a8000c07a2103610940080b40014854006020481080b0f540e040c10790f41c020300181071101014004600400c0007920f0f9000401c0e0307901b0300c000020300724000c1c01d21480c8680044c100c02544d4265040c907100700b000c4007a1007922174070507804640b0914542c04c400c8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 157807562 1250 157806312 157806349
    0x20102150702010209090403080105151903090201110304090b12030910270e0109110a020a020405060402090d05010b0a0b070503030a1a060f0406181508071107080a0b0606030402 78
    0x5545070140d0a030700a114a441d03454211001004100500d5003001f0414120343c0b0544000b025044043c03000f80c1e00744101e103c408586076502c1311a50f5824800c2d0f1141c1c9180b4418108040d03820103507090076195070440c0c0c0c4004030300c58841d52018118200b040c42050f00c4070001004604100c100000500700b0140141010108600c020360500c0c05202042c2a51501484403441401c540d100d00405580c0386090142812460414040c0340e010002201180c0d08140ca0b5406480010324035820040a043c001e802c0550141d024007000c2c0b51a6035592249000a220f0707400002c00d42400002d000107114698081031032080c0500410740400d0000c41129401251a600044c01e06101c3d24181c1c0c04030503036071160303412210201c2c50440003008400104151421925030004807501c08540341d9984070725005070f00000b840c540841c0d007541d0042c0c0000d5000321307039030403d12480b0340c100208501d0b051440c0c0c0880c0c2c030fa900c6006d00f1018040460300551304200140c448624500c1c0c980c020038a401c8086800010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 157808812 1250 157807562 157807603
    0x21005090303180f04020406021023070807031d010207050d0807090306270804090b1c03080a0f150603061202060412050f0601030f0308181b0103020408100c1704020102 74
    0x3ca0340d40f490104800040000d004640303131502c07000025510311203d51076640042c9007100c035211449020005410890312540154150b40d603118040390103400c040c01580505854100c19149260840160000400d03000b00040c0ca071500b90800364130f4050320110701c4040c000081d0038000c0302c65000d504507083e01d400034000700d42003800403010702f00000e200308120180000300740840200500c80000300f08603440c00100f40281a1101c00b005000c5001300e42520110000f4100440064020500954002c0c2c0c92540002c1400303080c0c08000550311074007848441900d09030014000143c15100700d0b40a000c0c4910052080c00c100d50205106100d42d015112650084601c4402008020484410201c0f9034038140c503000e507920b140c95426a42c11070313000c502251030800004d81c2884000c1c500c0581e003c1203001802107400840d1004006900c0c103800f541099020800801d90345003c003d11046c41034208400904511007180007002140c611084881903a840d1052002603a40083c4c07000e22102c443e0315245 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 157810062 1250 157808812 157808857
    0x100e0726070603140c090607030c02030c0d0b0709080f0a020405041e05070501090e0f060f030a06050c03071b0f0b0606041206061701060303080f2a07021005090303 72
    0x180aa00061800003070711402002103506581030300081d4100081c1100b2150035111640c4100c01070007080c080c00c0e01f00900344659004a44182070200741d0358005001e80c0c000110b0031001c100c5a6103210b03010b48042c0d60441c103020031180d200c60100020954403002d04403000121030706503100c84020b032019115640702c001080a20501c400303800003a0303010042001c410405468034580b0b81107503110b401e000c181d1083c40005c00010600e00944115400101c0d94040d644078401c224440026030340c29a0188140303c0b00200149003845294081e21070f14012984900d0500f400500d04c2c4100c00070591f441c0e00306240d4100150250100e2071300c0c0c90380201d02c070390303250b40e420081056409140e0205000c0040d880e1b140d020f010055010805446082440207070303004102c480395003a69150b11000740012603550015031585480702d29190000e4101c0700c0048800002c1035001c482c140105094030a0240c0000c00340c00310726002003441d100e90703540d0030a18180071046001035140c2c016901ca0011022002c040c10 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 157811312 1250 157810062 157810109
    0x2a06050c090a090605180103030e0d050708030a020c10020d0c150b0402040e0a06060806031b04110301170c01021617010b09090c011103070f1403070209010b0705100e07 74
    0x1d80c80e50030042e0050032050740d02c9000101078041c0c0d128960264009204c0950355403000c403083c9041e42e8160b1103c405400c00701c41800302041c000b603000c0d1214060707140c000c54514014001002c0400c1d596009000c0d80030048100000c2c02695010340082d03511640d04104030503005850010050303000117070510344a210001d00d0780501140700c00e15522910000d40882c1054024020a000748501c030310130083c180c1c50368010348001c10180d03906507050f8030001c07000000751f00c1c4402d075080106002d8004100912281d074401e903d80c10a80100c0c01176011444030f840d80800410640d8001c200034401800d04d100300f40c0f6414007215886c0191907414402d090b28101b501400d400550b411000904003800c1843c2c2004141d0300d0b04a40241140081c070449500b041b4100000b0a072540c50b90044010100b004050790b0b181030982c0a262001210b00081c000d103005a500d8000c580e00912001024aa841d44035113800c5003408850301c0005640e81c80c3c07141c0080840d0000a8510a4820981c0503441c0c00506407840e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 157812562 1250 157811312 157811317
    0xa0c051c02120a110601060302041509180f020d020309010504050d02032113150501080c0a0302060406030902010c05012d090b01050f0a080708010b01020d0815060304020a08060a0b012a06050c 84
    0xc0c0007a52017448000505285d06900510443c0c820201d528801c06c42e02a04841500d854440d520540312500ca40c0f54903251154820f0f10070b481c0344080145041d142c0b0038018280d07001241c2c1014184d5551007000203100041c071045130f441d112031004e580350a40059886419103024074140c2402842d50740051280401f0a1550300d1454028105520000d04e80d05018041c00c42400313075501e41d0284207035950311420302032840015298010001803d0074140340d011001010300c100182e041004a409000100b5000e102e40a85e4034020045d008241c182d171001130184990401003850440c1c0f414141101207180142010b040d16011510b005181695a0003d00b0f140c59a401c809101c0c0104d00d00000c0140c0d055006240680003a000d880301c08079640c1060710300b5401207901c0c804039080018802190319005005551091006111150107512000a0391034002c00303c44810009555484413103040d1707044070a00d0760707582e100706450f40240c21041c880348042c02e044400601e00c1c1e842d5004100c0841d150b00a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 157813812 1250 157812562 157812587
    0xf0a021c09030e01020c0105071214040306050405060c0f09130f0c090509010e0c0a08091e01020a2012090f030613060608030301050109030305090a0302060a0c051c02120a 75
    0xa011049903090050316004000121049020441e01000820194004600c6920f030401c161952400d20100340c8a0048002000c501d880410a402022403440b400c2d9101a001550140400060301d14052400c43e10b00310001c0d01d032403503021041c0030b010740d000c000a044030040e00302910681d16240c5c0744150b01000d4446907c5841c8403500308818042c5d141e502282120032174004862801982e66210700d20000c002c401c1e00d0a12039007400304541c1e640a80100001c0e41c000022100b01c0300b0400c0071701d0302e200709651621a860f103640d4000402c2d4002c140d0208031030442c4802011403040e1071102e000d80700d981d4400f4030711100c40c0000c007080e403a503d41d5a03544242e0708818064161030305c40c54280c44141c1030701d2000070100c5e0070500e000300200e62280300005507416110180c6584540d10300f10303101595990002c2c2080b950140d1b403400302100584802001e06180e010700e071a4050000300030702c4c001d81412056900b4422420400d2000180c8550002e15514040d22101c070342550381e00310440c200c40c3c0200165 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 157815062 1250 157813812 157813837
    0x50a0207180b090a050606300c0903160803040501140c070f03030206090109120c0602210709060203070b1515041e060804030c02130e010908071403040e0f0a02 70
    0x8401160307100d440e0400c0b10300304000c641e101a907580d51800c0d507044a6042e0707215500404203002c0c0000d43c85034004c0400d0075002c8608070400e88050308014031000d010071103189540580c0402c1c080c1003400d00b0081903d0b11340501c96100d2805013071070109a62401144540c904100d05401c10701d890140c0c02c0101c44103854944140c4500c42e8031461000100c41240c4401c030018071542c00028003190040c4107803442d095201211966065040d4000c461070320311b440099420540c20001d80860100203e54000303803150ba8829210103140c0880090030510040d40031300c0543d00100110000501e034508919072185803011845050500300c401314942603600b80320540d11031030004021401050956001540d402c004060454083d201e05040f44c40d03450582e0010045081c6d0030740400146401c0b18404940041404006801d0800c1c06003982520405442900c92880000781c47c0c061000c218100d900601c4260001d602d403624000107010b5408008000300640109030010900920482e0119251070000c207 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 157816312 1250 157815062 157815089
    0x60c090314010b19080a020919090308010302010e06040602100513170403020a05060403030e0f040e070618330219110306060f1005090d05030a0503010f080c060406050a0207 76
    0x316124003c02c075280100380b084d4425002c6806085540c000c80e0f0540304030202400791015207600780f00c0804805404040c905800c01c081c1545200e40d8800c1d00b021a00a0703440000310751660001518403d00242401c0c050302041105108581e00000c0c403180200900c140000e040e07444035181000c83d0110400104411445c1005003400100b04016006480c000c44028410030790b15400c1058a200390f20009000c0f07010b107400da5100b0f2600b2414100348000203840483d4843d20405002d0a01c0072642208002c12111101c01c2c2c0004402a800e40c0075110f01c9071a020405903040c00074600208608011a8a0281d60900001c85200303200110b110341c250300601c03416041c41d141000c401110060268064030031100090380300e24010803110540300000d09050850600100100c030359621581c116904003a40c860300e8400078004100412a0364019540c80d1f0302e035410007140d40d444900551199000794030408540318165101001c550443e003d500b0029581c01c019001a403c090300c0d58000e02403016030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 157817562 1250 157816312 157816343
    0x30b04050303010905010f030209040f14030316170f0f040303090b0f0103060e010c080606090f10080906010806010f0e091e0d021204030c03060e0f01090302070e0c090d060c0903 78
    0x2031070580b0040755017842260380f60031901038124040e20002c0e5101a03070401090104606560304a2818003952100e041d04082d060310614507801507501d0202c507941c49000c0e21149030310402c841880d03200325070050090700b00b0b001020070010340a41280c4105806c0c0c03010404241c040e0f403103d03000540c0039229140c00e1521070300e5001410001d120648015040030a456454035041c424192100c0c801d031680202501c5410501c900340e00000c4005403c01081c0b80051035555840c86003030081c1000b5518040716103840c9544904002060303000b030390690700c81c0c001030100b4a0f01e40d0004059034451003a420659841000c030030b141100401640590746018024407800841c0802c1a0400b0352998003211030a0007900c3c1030b2100345c4502c2c80040e1100142030000d000041c1503400c0352404070b0381c0004560700017140541c41401c4a40c0d001d0201c015078403900b4100305486010003816440f0798528059410320002102244c50400800f000502c900d55484201c1d942e980a540004c01641d000401089174098 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 157818812 1250 157817562 157817573
    0x5011404140616030201200705060f07090b0d050a110408030306040209040b09041b060504060806060f040b0a0519030c0f0e120f100b0402030105100c050c13021206030d090509040c030b04 82
    0x564100091100301400c0c81076090f1020002315058950301c41d00030060b41c4d66035102c41c0e48240d000340a41040200500c00046c1000b9103601805266007028000507150800c02c26182c00c440c051703031212006030014003040004410100c00d07254040700c00d4801590781c501c00000640280800c1f400aa40610100c041c031040c04000540400784001d000d582050307603511040c0540d1280500c0c82000c00183d29030b400100c0c41d017022005040c4100280000c0c0e070070941ca500d6103110030341291044900084000c21180703034005140c690240c0f001c49078182004070305641d40008000300d200340c0300354041c040c26507401d8805403206040841c1402c1c988094400100f48d034a6a980c4407040618030689443c280341c022505441d040c404c8a040b264002e011941345018140c5c19a10300c0803c200035107a50054002c4010180c0341c0682054258010f8800140c0d1008250b807444820038014218901951085100700d52141d04000801c1c10307614101ca00358400e5032a8502000f084105800041540743c007441072208000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 157820062 1250 157818812 157818821
    0x1b0602030403120216030e04020705030a120b040c050d0203040c03051e0c040b0a1a09060a0c0b0a0606082719021f02060c09060c01060303050301080705011404140616030201 76
    0x340309558400a90f0501160402a0700070720129001010310342d80201c000030302036640d460f68980d02600150414080c0c2e140c0342e055800986d14040070541402040f0320130f102c6403103281c800407003c540401419020036030040c01c0b4090f00703901c1c0c008554004042030901c10b0120301d01c4c00459012080302d468090b41d02031101d48600d1903000c0c81051240c40600f00107498a0b0042c41c9a41d080a00000b0840b4030f8020402c20071410140052104403080001b01043c0d20f603000101032503a09502d03030280303c120515000d50b10440060041d0080d1f0715190043c015542c0c481030898021904040480340d404501c949084103100c03960342c1040c0ca10030950084e640042c40b20340301d2056802160000141003400d00306610501205c40040c0042c0c008600040f1419144c2015000d003a41c0500201c1c00c0c004000806404c440064000790f011400200040100320000c004440180c1428a080c007020310440c044100c003805240641040c0a1240b20441001d864110554066800d01c440d40c40c1c540f031650402a0081 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 157821312 1250 157820062 157820071
    0x6090a060305101806150f0504050f0a05040305120c0a0f11120904020d0906090b070503091f110c070819051b061608030403090605030402030c04110903030a021605121c1b060203 78
    0x181f00a9400182c1c2e140c030348503052040249088107201c44e500e54401c0f00090a006000302c0a0081c240024204441e80c43c00d094425260b614656542e0b03445450060444291a11400100030090444903100701000c03071000008480d20400580390403161001802070701071444e03072814161804904000f40441a006440c0040c0a0083c03404a5210405e04a510307110032104040c0b81d41c0084003000c03074502600e0b4980000b000c503000003e140c00ea41821205d065201003d252440e40c449a024484008240b003403c3c02d201402c01628210f00056513001e48074101c0000c01c0e16505201010130001743c0f2501c045440381c10340400d00307071802e054034509401d10f60825501540000c01007500030403039901070000c40e401140c00a00500d00083d552040001920700000c11501c6030300d051004140545080015021011260700500100d04000715a41e07408007042d03201d075100d0035003800c910504010200c1c00b00c0040d1002508044000101032095a1040440307448940d4071300210034a0040c0001540518001c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 157822562 1250 157821312 157821329
    0xb042402130f27140103030e09012108031801020f130605070f0221011503020102011109010801150c0c0f090b0a05031914100506090a06030510180615 66
    0x185502e5809240101d003150051401d160550403050400d40059109103076582030386000851000c2101c001c001c4046401e90040380403803c1051412001d28140d0502030140c2103281c2c140c140c00c2d00c0741c10781920580a8001c0a003800c04000003140707282308440400340e0072000e00d0000317541d1036415468902c06544250510689404001d00103c1c0e81440b6030300703d9014540292610220784415020000341083d00399501411103c0b150140201030000e002d0442070002c011401008280345000182c2940c1d014400351401850401803c4016a0400038460550740450903400310100105002d84400d1036045024003020f0040100040d5428444520015104040c03000d0020643c0d81d410710030382c040513000342580358015114016004002e55007100c50790380146414149411022295030074249214159169541c03141c1c10081941403032624150441000308041101d545151076080d207406102030038860941c0c1750100940c124170060208520aa00540100706000b403e111100b41c100d07540c82240340c1c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 157823812 1250 157822562 157822597
    0x30d11040312110c041d0109030801092f03040c03080f0a09090207050d050a120e010605011112041e180506010201061a0f09010c0b04060903120501050d0b042402 71
    0x80b07041c8100c6000c00c111003e0001000681d04080421014158114040d000000b1790007100c0385c00d91003400380720389280c001e0311007480b1035041508a000343d030002d04801030340c4900ca000e400c0c101c104614610307002e0b40000f204139442c1e071910718006c0300318002d60b0710250140c030004c9040b061811804000f01904006900d40c42c50290380d03190342205a004a42c4081c10603000615084200d9000350001d240c50100ca103005250340351410f50403400c5a081c41840d400c90380d550082405030796008244400304c42c5c0140001d16011081c1201200e8610480c040d520301c44403a000c525111401403840f20002d815000300d401d0500381070155503001401d00300c40315401036003081d0002a0103550b48031b00004400444c682585408000d40b024105a4042c810003030412090b0091000800e00000829004500c500d40c04600c504450900501494102c07e41e10f80c5203107170600422442d6a00d00300140841e0b40480f900480e80d9a82c100003a9000c1c0003c01d00790700c100c240e501d13881640ca15a0041c09d0f03100c40b6400115 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 157825062 1250 157823812 157823843
    0x501060e2511030306122d011406060403110103270b061507060b03030c030a050d0b010503010b0301090c0329010909111213080a0c061803050d0e030d110403 69
    0x6541250b611000a038030703003040001c1001418010040c1c0d07040074a1908507150040784910b50410310700d4000d40d5000050b1100f0703072204100e10a008007160385401800280701424814000f803010702c2103100061441e0b01c0084d50150360b901036007004142601c1001e500300c0020410808050510940804903038800c03500c00051050701e0305031591103040b0304001289060152584d02c0c0b00061201c4650681d0612081c0321003607a036001007000b0440040d007035642c2520ba210780075800c010390f905440c0300c5041c440d041c0f0060021102c44c100b07481c11a01ca002c03000c40c5032110110f09034010020600c0c004020b29029204400b601d440d90644d130410002a80c03a404016500c580a40443e40e0800c5407205001c000c01490300000d00c4806841d0700025009582c8104c0d11140d0344003c1d4560010110301c0c0851304000e454800d00c005441540142090f0b4100d00000d400b0654000300103129141500c2c40701030f56a40b01c110406010030640341030506045080064883c2d00c0010002d40e0013a00c800c4030b6410000722400d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 157826312 1250 157825062 157825067
    0x9050103030e09071e120e0604060207050601060e010e010e061c06051003020702030604030c03021509010f0b010309030e090a021314030d18050105030727060912020d0204090501060e25 81
    0x20420416203805c8070b092110350820850701b80340606060303640381d40c0782e20a1103010381090106502881c4a0b0000696808562800e0b40c28004140e102d030092002294804102d40d0f00718103007a02c0d0100c2440d00040d008075040000c0e48600600031030102461001c410400c7c0d201450b84014140d80040321841070303c0d9644c2c0811400d91066090080d0942c02c02004100003c1c002c40340744903050b2180c0107480603580604004205624202e807440080e0b034681513030b030440e002c00340300350a000002840e0a11000742240c03006040e4005079661140540d035000c000892005507541610700c0c03207850600d410803ca81c0c82d0036012000940c0e80301c682c0719000d0400250a610302501c482c17040303100c40c0c81c54110348528020055805410045c551418001810309203034501c503a0f015092000502c4070380d018106410712a00802501781a0040159000070421800142c0e907215090038603542d0446010034010380c0e52805d035015001c2c1d0341c050351600c8420001e01100340c0c101c031400306032200d907281642c00184400004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 157827562 1250 157826312 157826327
    0x6060305060607020a121a070804030905011704110f1c020901141c02060f0a18051210021b011401061116031506050a0f0512010b0306010501050a020709050103030e0907 74
    0x7940008045c008110007001c454141036820300403081c060b003041341001c2c0c02100ca4022245500041c0c0100108420550010003800c003500c820b00e0041c40c2c555011136100c0c002100604040c204c4412180c0d000010394070b40407000d404480141030303440175190804c252410301e10b42070390880c45654408008150302c42980c0204003ca0401064001403020421004086400e0402e09a030004d10030031190503000070b9a00240200c0b8856666500c9400098400c144449210780215203e10300b0b5102c00c82491000040c42c0d200c0d0712100e100183c4d220401e4090240c06a412040c00300c0b20350a003603d1b0105801c0c02c400c1e19040301c5007611140c4c3d101c15042840c1d40c55050810b4401b01040c6070380020300204004680c002c0502015050024509443e8800507800c0705459000c00b0010083c21014400e5003070021014010361034000003405400e9007100040d48071a0305004150402001064030380b0080c0c400c01c034030402454428420443c9507100d060090440710041c43d428010082c0d90003003160140714684 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 157828812 1250 157827562 157827577
    0x304030501110304054c0c0c030801060f020309271e0106080a0207022e0503090601030f0203070b0f071a06130209040908040e090d02060c07060c050d020d060603050606 74
    0x584261ba91b07032408481c4a82c415140480c0c2c03c41c01c2842003c0a1038281003481d96644d00d41e0b0305090901c40700031080155a13507075070f8250400c1b2140c500c20001a80048030581590550308041092200080c0100d03d14000c0d92011684541e5410825141550041c03d04079400244141c1e20307602e40d0f4580810f00c061070b02d090384000d64552100108000782c42a80390641200c2c031440c0c05031501c80150002142003e0040d5515494103c9145298510f07c1d4070220745151842420300c0750a514000b10788940300c51051001038510840c0384802000c5540a01c6084050441046099240c101c1010a58848d40040c402100d07114400303040ca602e00601456110311412004005a801c00c000c580084080d41205034020f41007515558407800040c4000050809000c1289552540d4581600460700e020500002c0030155001003080c800d00707406240803031780300d07a4000c20b011424030709140003110503105603040c0340d00c443d10214544c0d0503009140c001c00d044030180e0390180500e40703511003086064441e259 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 157830062 1250 157828812 157828823
    0xc150711060a020a080f040306090c081908070b06061201060201200301261c1214040503041e03060507020a02010306060905061c0f0212090111040308030609100b0a020304030501110304 81
    0x142000003d00603c014100c0281008904c4d087c681e6990344d06050b1820050110b031003044401c0c091150005c20001c40048040c080510910480a521182114070810074017801e5000f00000044640c4c555204984884a0045602d0082d6031344010013402840c103452002861280d980145d10715840c07039001c0d28140da00000c00c058504c0c25042801030444046007000c2e41038000c1601c480c184058480c240c03024121151a904078010180381d00c42c00310742e02c84c41c0b0344401110500c144004114004281c4081e00c40c1050680c0852000303006504d0451310f90381c401060182402c0802540c250701155032800140b007030700c09016107600c03000141c508510a02071280c00160500402035505400b901c461880f12050700009117800039011800e0681c1d0040f80034011210512040c0030f43c0d40d009115201507580d02c814220300702070031030381c501d200342c84050f04a43c42410110081290070151468403001402080c2c4415079403000110702a48980080c03109031403075464a80d41003008042c04040300c2c82150b004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 157831312 1250 157830062 157830073
    0xa05030a050402030f060a02130b0a050a0f090503010c050406110f121e04060306031703010b030c09060c010915060501180611281202011a120c150711060a02 69
    0x30501500900004000b66031601ca4030f0741c40300c442401400440d02031118080c016a45511044082050004039400051140070400c56160410740c400c0958169813a80e1804000382990f4080031a019451a0026070f4154030b020300070607010360448028400c480d5191200d9209038a980341054603961388109110003a041001d61491621800004180300003801c0950082042c401c0020089038105820900104e0741d00e48091062044007040644400c12841c001442c5605200c101000d07030101805c000810f10020640d40d041e6a610001d03998540c00d200020000300c0800d0420441d0a01c600d40c540500600d0b102012510354400c041080c41d40c011551310503034403464010215480e8403094410030039030080505000280300709039484c50b601020729402e007020b1ba07154206031115480100c1128150781c901640071850103035074104008c80d10800c443e8101d80754480e2103203030308214809518a921021180c2145420039010740500041400384020b50342c002d02c2c1c041400550302c01c03110040c0160740a03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 157832562 1250 157831312 157831321
    0x106050a05210108070b03010317031003050115060e0609030304051002010902100c0302060a05010e06041e1e0c050705031204241b0207150809070f1512020a0503 71
    0x1100149100d621515040d4501540e400c50402c080407420328803000400c81c50010002c6900800440018151101c00d040c42c2d5495651008820104140d28558030100880000c00864854501600a5400000074840740060781c2080440581c81c4c00703540702140900d000084141000c1c016034821441c050001c500d0f0600701003c100440400d10050011503403103122020042e05c80c0d00c0840d94450b9940ca40100341e80161402908200c8010264090ba516000c010400381d14081c0070741c0d800100558000821001d0803910100070061072611004480c100040e0b41007196115000b9410704d041002c0c00c0200a40464044032103219031400038055a0003404400078401ca00c0c43c225402c03911900e02c0024035800e4060300c050000e00c891100c0e48007507070b842c489450208030003614603003050301d0b20140580307a003041951084812203c10020030001e2000024010050400202003c1c195910792001c5e440d55070000030003081801c1c191100022000b4900f40310401c424001c0d1130100d0f000c0c0e11664190360f903 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 157833812 1250 157832562 157832567
    0x50702040b0d12020601090c0309111216120c05030a0b060613031a0402040f050402210c04020403060b01110304030c1403011409061605090607081c06180b12060106 72
    0x10801d036903034414410103003080010741211000400050300d40190803e58034200c0c02d58115110b556103c0d051509101d5800001200402d0b80140f204003100ca135042626414801031030030140a4298400c880c90b04808503000e4040041d901c410343c440d02d900046070340c1724400d00d6190444948018600c2d44130074041003451a041b40070f8118400e1614942030710599076110500e460070420199020811410144010342c14203015002c0c0c0014081400d201e42d0509502150046400c41504008010150417444002206001071100400c0c020030a41d12607880e402c201c4000e1510002d12800300340d003e2045011003201100b81d0b411250800c04106030715143c059000074452a4a5415a0656903001034018009148446a000c4c12824009150514180f40e8140b10782035400303040400e00c1000e204880c956618802100e020981c03210380e00341c880303442029045068040082082106050210214030605411080c0c01e5441400d0f80c02e1040d184400c1c14840c0240e4961100d65a42c0c00c1240188103450 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 157835062 1250 157833812 157833821
    0x8210a0c08120a0c0e0402030402030c060d0209030604080a020601061803020130050f01050d0b0604020901030902030a050f28030c11040204091b03020a20032a0f0304050105070204 79
    0x40c0034030801d61900315101d400740c5044004942c1585803d686602462050750320422408000100351400c42c910704060300080da803941c120400e184501000207200c0114000b68040d194152009411100b880c141403601c40704035081200c00200510607000002040c6101d012400251640c0180100c0c0040c111307001140c1d82010100c680300c030000d2a03000c1d0780b40c045944030040101c1601c1c50b8000748e14146502046034000c0306034040e51242542ca9855404140d0b444d00e2250008030803100142e440c1c03a0318005030054040440080e41c94002c0d940c8620900c480800c80000c1c0034510400d550b5014403510f4410074504480d90000001c2e6204910031001038025201c8188081c0900d0b841e11081c49000000307405d80c1e0050308145812915031607072050007104001180306121590606608107200414001d0410f2031800c1d100305c9a1034441c0c82c08403200313814812200d031a0b040103e0003040c01c03a4aaa40c02d8501d580051000a40c45220044070000d00d01100361400d50307405a40380c61074034120382c00300005403 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 157836312 1250 157835062 157835087
    0x310050f0c070f0b0a1103070522060e010309052803020c090f041b080610030b22080706020409110315011106010603150b0706060513021306050a1b0c08210a 69
    0x2580e503a41c6c178020030144070f40618070580f11035582c6a541e1140d01c0d031030f08030032040d040011841c0050036001d01074982c000e0240010743c0c6081c64005103618907030810307915000f4802001102c04200e040b4540d60104042c1581e81081d0080e0210b407081c400d603605202030080c088a40c0310440c40d42c140404c00003040d00c41000c8505a900036061220340d1144469810600d09403881c00d646803400500300304010700850113a50290008848201c031081c0307082c0501c0c1c21041400b006100d02d400160030000c200e01070f415140a8420103104011540b904503404c0c05590044c1c90b02507000650f0802084a98410006511960711000103056503910b8514150702400016220451805002c440854030b5280e030f4019010103409030201060303403850710040c01000d110f01c11948034441d00400980040700101e891000848540740381c80d50342c402d20690112602c1c1d9100400c8000d021001c120b030400c0c050722169442c290f44484040c1c440e14400c1d94940d03103080009034001c4400c10000e116403d1b0140c0103000c0e44001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 157837562 1250 157836312 157836331
    0x8060a0e190e1e0d02010e010509030f070203072c0112031d1c08030f060d030e0f0a03080304050f120703021c02152a040e040209150310050f0c070f0b 66
    0x4002a83c08034807039100030582c2c221603c2c0d21501da00710540d60709025800d08140140b000304214100303440c8180c2c0b2440791301d6085d241d540001803040115241040f02100502c44041e44060b00344c1000407001c0079410314604081e11044590000c10719070800ca131801d2140c0c0d4907444001c0343c0000035810007904251806aa64000d465642d942c072a000252080c06d01580b003000c806a070780c070b002444059444c0001c0c08690050410b50300c00b40000c2d0300080c50b07803c054012602000b590002c440040c01e20a496000207141504c04028807007003204c000307000784900e05803070203440c19600c10400701c00f0240298040a001a840401c0001c0707212501460801080704901c1a201d03d0759014100d4007450f03200351402d000034854100403100c00014500711030011100149104c0c50b0030301d0405111001c05000d000a8400c2c030007000400c0d031929402c0394001c0750103c05016160480f2405144000808049800c945404419000500c4c559010422034044a41c40b010040c00442c19031158030024034001c110524 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 157838812 1250 157837562 157837573
    0x1216020f0a0b04030f020307090b010206010603020c03131e091a060c030d110c06010e0402100302180a09020702011b0f0f06140a091506060801060c02031c08060a0e190e 74
    0x30246402d40091003d18000c0c40c400c1701e50901c038810325103080d12981c0100003403403800c149910581c0e03000c0b90032411202c04e481c0240c1c4a9403881b001d942940701c0c000b40340d59000c10401300000c42c000180701d40d00b803000b5100c1b0031002c0c4656030b00d0f003003042c0d50031020031001c80c9170800c8015145180103000f800189601d42c003180c0c10b20609003a0b0364200c1c3c098004403194a4004140510b40d4681003051501400d041c40c0d81007400d09043e0b0109070340c1d0422042280038190042000c003400c0c01c400d07100d01c2c20444000d04500f03080307544180641c02503100280aa000070440819111480365810750380403030782d0b800074404150a1058071000c84c89002c81c003084801e1501c0c1ca801c0000800c08290aa0007048500b500007040000361900380d51180d201c1c1080d9038064213040d03007001403d4110f0a06411219607007000300a10305d15100003414040305500d0501402c02da9510710300000c0d40070700703481d102e000c0540383d05504980301d10003006440d008039403001d81300445003c0342c0030b080c0700c64000c140303000c10301d10450b0b0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 157840062 1250 157838812 157838819
    0x7030207210b07050901050d0902041b1d010201053702040b0901030e1504021504050303040306020405040b0a0305030a0302130305010e06090115230114030a020406021216020f0a 78
    0x140212003568011504501003216042030288101c0a50f8000d801c50814074a4039030088000303010f5008207140303c1d000c142c0d0350140e40159202e540004600700d5696844560014110b03c0c05490401c00c095000c45000e14031002032580c0d40144500d502907030075400c4991190b0300c2a1030b0303007102d03100c84840342189040d4460300720048012400500064a0040d159545607485c401c001011207000640d0b45c0d81c1a8842c140c5e4403180290501107603000303501a01d0b4043d1505490040032014402c0398049601844001000018419036038082c20a66400b01c406024000f0342400700310b1442d50740d000c040c00315003081200b0316845010f6030007010078100810701810035035600c0c2c8405003152000440108a40c124004004041c00203101c0d43c4455115401c42401c0e41d400c0c0700c1e1001d0510190146c04028003080112401c6e02d078028203607005409640d100303140d40c80c507000001c1d4020703420a108100151140382d081803003a410960a039990040c10402d06280100c85408004880b5019641c82e50040400a40407 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 157841312 1250 157840062 157840079
    0x140906041508031611010f0806090903160602040504051e01061d040635031b030f0c0f06060102011a040f1410031b030503090105130807030311010f0606020c0607030207 74
    0x2040c4038609030821403c0f05a250600352440005c4021181c10000c2007588402c903603030000c0503580c11004c242c80d0b071185e9984d00840240b4511030203150342c00d01e110125440c01001071540040c4280c0e403080d2420301c2151152203010b106040140d2450040503005401480407500c2040c04064034044103042c0c01c1c1d00ea142070046000c80340c3c10f810520035045201d12000811000c0508034000000041c0c60040707400c2c0c00803626469000f241080300c00350380030035684d0303014030810810740d580c43d4803d03154565146181055256950000c0d0124642402080006480c1e0340c0184200d42801ca600c2e4450100c030a40541000020510130504100d5540c4e60890080d0306901c3d03c600910a540132888083c040c0d0841c100344a0f4a24a43d884000c103100e00701003440040c8011040e100d500da000e09045444400e0401d102030701b80f40c150004101c1d0320030b080b000420702d40e111444c00c8104030bd110080249001d416261801d0700c40ca07020386000b5030300071000c001c11401d10340005c0c81c01500074030542b170721701d40c444005 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 157842562 1250 157841312 157841317
    0x302010605060f0d0b031612081c1d01020a090e04020613090617010e0703020d0804151d0405040c03230601080d17070905010c06110309010c030614090604150803 71
    0x1100c0e4800004213244000220720b11803e500700f0302c100d000745415040172a0442c1701c40c0040c00f61109041c100b6004104010b102d8059802014000c0b034004c40700b251451010000b0038a14100090035041500c1d500721829042c42240c00c0e00c001030fa100c4060303901300b400840f455140a803080341c00c851304200c841c0000044108e41c001809200c84081205c1d45009110340c400a84140c0c0c4040360b914000d1304c2080d00100003160760032651305881680b074142c420b0400d4111400303654840302d541c2c00318804502c84242c0c4040e000f1482c00c50f021307090f0b40c0b00c0b0000091004440d0300300c0303008000c00d00c0c06100340040b90f5040c0c00e03021207640035201c5002890075080c80f0390a006003030f0b112060381d42c0501c0e00d680350290030401048100e01c442250002034640018020518202881103505200401250009010301a08840b0b101c07004c2d408243d58074105000c00c18024810000031100003032412034003044408010030198027941009103403034056190b110802000741580903005244ac00510300001d80c20506001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 157843812 1250 157842562 157842577
    0x4030f0b010e07050906190912120306140319150f06140301050910050408090a0305030901030501080105060105092106040f0303051608070e0d0b0a06081203090307020d030201060506 80
    0x8039889107500d41804050405409003c0c0d405004082c06426001e480b105c007525541100d0180c1d018903900c0130b480986504205402280030500381c00008000d00024011410005a0b07545e070400103181c0d0780a5407201707481300034401d585c9a000540103a411004003002c292040d0700515407020b030307040c0d03025960302100c15110f21441101c0d01e52a0800203d008100410454801a8000c0c030051420040450300c0d0f40b0743d00c0707000c81c1d020754030008501405511401e4030030802c0080d080261090f160b040c41983c035041007035a180041c0c100740c0042624441030180501868040e154181400c10420421007040d140c0d20729042c00d1040b081c942510040c042085502583c02050031070f010103440d007402025260000c5c010000412078580060701e49500c080840e038482d81c1450314440c24005140042c02c4580341d00c0f00541041030b10b505001c040305041d40100101c6119600b2606052082c040c0c0e284a4001140c4201e01d6400c00d00082025040407041c01d84031510074800011604c1c3c480300004c000e81c002c150b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 157845062 1250 157843812 157843823
    0x510060807050406050402070305190504030c06031d010e0c04020a0507020d140d05040608010302011412161d0607060b0a030501050403020d32130803030a140105010507150902010504030f 82
    0x107004005a0070305204090103400240e506500d4010151400340852044400e4114810302c04141401510b00c80c200359005164442901c191895803100d00901901c1003880c90561180314061034446030105200310021a40104060244030340c0031b0042100a41280c1010420300030304119a50060341c54028070f0700c0b054401e0f8800c070329662030f0030b1503245001c0712200d110060090403c001e01c100340c0c009041e9030449034246001440304080c002808140d008200c09070403480c466005105031a0841d01002500071603e644d0440111404000c20b402803056080080d00703e18108500b10110ba002d8000900d8190040c0410402990b20380c2c3d01e508440e0122403d1740142c01041070f69282035404144060808142205001505040c80e041464410a110500b07000080014525070440c0001d01c3c1c10007d00700d000569840b40342000208005d041240003e4202000c0d410022031158001d0382035803107098110405924040e9110407c03070040240f0003007681840070600000002800203031903249600d1241 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 157846312 1250 157845062 157845073
    0x110f01081609030204140901051e060405041401020d0501151403010909050c030f07051806061209010b1801171f020a02010204050d081806041203080a0608070b04030308160e060705100608 82
    0x1e1085821140e016118540c1440c0030ac1c8102c0380a108503a4050b0020400c4a0005194445140c01c6000d040011343c884d840d54000301c0c242180740c00580c0003134101d8180030040070308180e181d007088038401c200c00040b21002c4414070050203d4601a8414a200c9104104a4000c00d03c2d89000030300c0c12041038010012030f4081c003024011400d080f44814032010401c40d513117a150400390f0004113039014191207035030203280c0a0700107900d0580c00d41020700159409001c7c40312182004451206004090103801940c100b4854004041940054400d403044841c89203013442022080c4484065801100072408641d020300012071155a44451160191701c02c61007155a06800c0030316038401004c01241c00e00c5600b0500c82000610955556044183e030b251034880c0803560750081840003001140c00608042c81515408a00d40503004010425a80a500c5002869035002039898240340c0d4501e10300006aa251210100d03400c10744040c00c21603200320151482c40c0344030380e045400c98030036038021265036104 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 157847562 1250 157846312 157846321
    0x32208070902040501090b130f060e03010e07050d03080702210a110106080c150d0501091e0903050f030703020c0109051e030f070807050a060f0603110f0108160903020414 75
    0x300110340081030007180a500b024601320000e060800113106404441c600059620b8030480440c20110243c82d0300300308110115114407000301802c8208520500941c42c000e14400c6001c80001d84804a80004142079422007030396500b00c0744084080c010109620075000c1d07415440600c5410200081c0c00254007586a04003080300170100d154840104d0f99991403e00144018000422110318004e000d40320001d1810454080c00154070070b03081a50a82481d0200100d600c1071980c01c00c0e208800307480d496a0b0f100b0302c240843d4040307481d0507400502140d8200517410402c003002020315800364440c200142064550f810080c04d40c1d01d003600441d040d0304120440d205070902c1c00042065000c00000442c00c040a03022141179600c160300f030140c4805004560241080010000c0310311031a0300441c1070040c3e140c0d40034990003030051404211070204605580700755030306216601c211080d505945c0c900c031980724034149003090398060020f41d04000e0342c10008800350322907019000c00c7c040d6440c155265440c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 157848812 1250 157847562 157847579
    0x1c090506150910060305071202180f06040b0703030506120124060f0903080c0304030c0b030103060b0f032a060a02070e060d0201050a050c03040e04120207081212090322 74
    0xc1d895166220340c80e20000d00c5030711000c014400c401d50304107040000c1e00b61502c1c0f00c01d0313858011801504030140d000103503110203a0380910880307040d0401a289c807644401c44500300b0400e80140d001d00442e00e5002d00c400d2000c1b901c00c0d00150341080000d4030102900c0b12072845942520407908031001000901c5000c9403544146111b220010b15080c40c007184840080c44000380040d03c58031005d440c070040030840500e06203091048400035079101c082090b00550f40e984142d500d0f0801d10042c2c413054684080c3c071b01241051035201410704001006000c800d03840e80003504c510310f00d6124070600090345084580058940703c00500d04d003942ca80042a045140074000c4101d5000100000e005100c0300c81543c0050360414240d6003401c2e014205151590312815660303203140103e500c60302e01084010240410300c00c074810030910107866642550145901d40b114507642c0c1c5880d140c91240c01004100c2c5c400c2c2c0c115981c044641000480c400d03070345001c40c0440c0c00860100710009000c51920007000030441440d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 157850062 1250 157848812 157848841
    0x40615050a0b030f090d2001060e10080f03070201080a050411030609030702270712020c0601030602070b0609060a0b0a0509060a03050708011712090102101a0a0b030c040b1c090506 79
    0x1117514004101040c15004c0040c02610707000b100707221405145640c41c110f00800e4000e04003400000401860a14006c000c18038908400e0cc10b0501e24003d0385001d0b800c0740320220485500c03d4040c0c41d21100c6031644140d80c401803400034001c1e01d03622181c2d02401159078050042034000e01e2040c4c01183c41da1100d004004d01e0002c0706030b05840c0b81180a2000f41e0300030042900c240d0013003003800c00549401c0c5015904010f8070440182c0140c9000b900b0000c4104021076003d040700901800a6988960b5050281b00440c40181c941c07952126404400f0400f03001e407000140040c030700ca403078007038105601900840e0f03d5401030074111000c42d4907041089086903000c018940100b10610518a2480050003441d4940c04414001703194101c00041100480c1d0080115940c0501300c10000c112850144d20301c80381d500380e6198036620a0f81d01c104000f40c1c0f42407400603032b4001d4100c41440b40c60a482c182d01d25140b54441030740201e194016009000740d80355544105910b40780100041c04803031500010303405518 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 157851312 1250 157850062 157850071
    0x604061d0f0d0305040201050d06060504091409061b130b0309120703080601050717030f04060f0902030c0607020114030f04050d03140f1f031b0501020c09040615050a0b030f 76
    0xd620210510071403580002d070741115074541e8280007595490703a00040341c1e10711034049081d40060a119000441d26030000061003151000e86040140900340901a4401c200555054000e076010601182d04480c400d00b103451402205484146072522030781e800132040c0c440d54008291482c0220030840e00c3c100074411010400c1d00501c46919200300d594016110a001901c51410400007050500c1086250341807038001004c06034850b074491600190450000c0000ca404540d2282003490781070304030840b400b0302c0072202d90060191840049131414402950070400c0c00360b0400203c0340030b00b06c100010f20011800781c4c4d11041d80c4655450981441c91808046800301c4003014940b00070b40c005053340051003900404541420300301030301d5520105945072908103040c900b02603000b000008000d00c41c0c81d80c1e5102d1126440315400e035980c40c001a03840b03c0100000913000701c000c10002e400243c1951040d40c0e024041e00207000c500741c803400030805140e0b86401c0b0090302d640000c01e10501208812409030310 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 157852562 1250 157851312 157851371
    0x90f0518070807060c0203030904090b2e0302090c1b2b0504171f020414060a0c081606140403081018110f120f07020a0b010e06040e060406 61
    0xe0a02e8032000503500c0b4018400d241c1044040000c8108658083c0110350540200400074040c4d800a0306103000488030680d542654210041c8003020603400f00701400e1050082e0030000e5140d507285070240060b141c4020000411a04100900e4038050264400b030b80c0000308200c02401e101c1d44c0752148080c1155068100f0391019825a008925160300400b110285c41070411006890105040c01902e03280440c80750010000b09220b501c0c05200050b80900301322200c80d40b1b16a00861480c0034059140b04880c001800103c0741220b200c0031401f007000903d221030300510180050a0395031111300884640108150202c191a000d100c207140e4460b2269402150b0760314501c000600d00702500c1c04450740b0821214100743c9a25004c070441c0710034800e9840f00c41442450780d54407006a030180701104012500351040d0250340d0f0210f03001d28030005016040e19404406100141d0070496141c82c945c07801890f0652040d1188401c2419810a0020901492107094042001d00c44024145101103031100103018 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 157853812 1250 157852562 157852573
    0x2070605042603070b0a050604110304020d060c020f06010e040311010e07030b0709240207060c050c0904080d020a0306050a150c170702030304061106070507031710090f0518 76
    0x155210040301c0318221090051544500c01d070740b2610500b5401400e03009407080b81400100983ea0440740c2000344552401c5030f0804c80c40b000d0314071030251350100742c6002c1e402003004c48041740041c2095011181d900c1c0d080c0100c0b60707410035400f034940c50300a00b6003002013014899014041050307080300c500003c940c0b42000902c420900010320740c0e501e1406110240843d0410360215003440d02504124000e885180406100d2003150007100494040d112401d10052040f2000024400c0c800c3d103515a90603400030180c803641042200300f04100d40e0140c810b0310b081c0810410f0500340000c9100401440c00207803804101e05203400b00700b1084260680c0074042c4414480394540480c0d0b4800b101c1700c0c02a9000c40c031550440c004414140d824015000001c2d0148000900401c0b420740204549030b000200004580440e9200b510860701800781810003808501ca64003880c824580984100380c2c4040841f48410b4800d44d01d4500b80140d905074030344d00300c0460341c0c3c006000340101441040080c0e24a08802082e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 157855062 1250 157853812 157853819
    0x5100803030601120f09060902100c08160204060510020a020301110336030403080c0d03021206090411090106260c0910050c1002041e05090106140d0e0d0207060504 72
    0x1500c034400100103904000700c13940d440c009460681c0c40061801291482000700d0384240c9410380c0240605403041e1300c5900000700601601e481081840c55503030f030010b809400d10f0310f103a01a04424040300d05c1268040c0e200c04020560740c44280e1722040104a0303a00a0800c014980103150071282200d0156002620030400c01034103000881030f00540200c019048203021700b00701281c401e10038503a9072031101d6000000380003041c020007902802944101c9415120f00c103041003010f60880c85010300348200d440078900050014a48043c01b140e00501403045044040c81000001c2c0e1000f20903081030b008100030031415450b140d10303d426600342c90b40450708403040f400c040080159a0040180d40c6100303012031074040f51458411070540300443c15140440c1c022440c3c01080034041d4216000d04003443c0c40440c140039400c00040c0e0800200d03803020742405200c0c0d0038020220307605504403240c010b0f402400c100c0440020800d00c1034007140c1c05284041d102c030004034080207052400b164042000c001c1e0070321050 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 157856312 1250 157855062 157855079
    0x801090c020a080f09030109020a030c060f020705011707120f061a07020f1c1a010501120207031d04060506040e0703140106021b130c0c02010e0102010c092c04060f0510 74
    0xc8130140f405607425600c40d80c5240000307014101c2c517070000303400c0820343c5800010044510180820f841150701d680148490f02e0004a80d40c14292044500113112288464840c101546655030808071501e0204240c44004800c441607510710312021074503e50b190410007500742a85200801c2e2000681c2003803074158542c000800d03190200142c0c901c10610340102d179240380a103000c044181580a16240c01020002c404402492024401c09010405800c030320100400c4601c00c80d03201c240e040d12a40d90f2220042e803400d4190020700482500666612404610399840d100034000501ca48080f0040601e4070600c02803d03594101842c0c40030302c01c01d00044c40890b40105481d0f025841e105030b496005406007000680300c0d024803000d28041c0b80703080c1f800421130340d01008030729801d8000e8850350703004002c06004a00300d030b90010104001545071031040c425a045a81c107107a01c0d02d8904441010318050075502e2807909000d41d0110f542c01c1d940c0c3d012400303111460040561001030303840c04c40000340c9440b219 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 157857562 1250 157856312 157856317
    0x25020f060913110c0a0c06020d0c0218090705061c0b04050f0a020c03071e110108010f1202060c0f0a0c2916050118060f0606140a0207050d030801090c020a08 69
    0x8054030b207511003640d0721200d01c110040e108498085001c46940003030a05100b00c5003081c0303001d10300c018040c4914008050b030003051942a242d0b03028003c1c2c00c180112002042d84554040c04d103441c540140c00c800280f90f580e402c050001045101c81c44820000c90842003422500c5107410b02e4004e509282c00c1260f0700c0108040150f110100782c1025030345504c801300e943d043d031260840050000d030841e008079170b41110102c0040794881c880d0007941300301000c510054070203000910600f5109280751100780801302104010031141c42c8080d000d07034223120070038501034240000c1a00c4440c03d0b6124481d400207000040b00c43c100140f40403100810f029024203081c6c420280d01d6024001100000520880c1c0c40540841088107290004000c1000103078035908060031655816058401d203080c061492505100d6100e0081103c107182c40312120079090a81c10303505500b00c00c040406501847c000000c0d15102c1c00b1580c0c1049200340c1c0c804d451581021411411580b50545040c110350003080814000740e000d508 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 157858812 1250 157857562 157857589
    0x50a0e040e0a1511030a14150a1401020304031703090d03060e010e040221061605180108040c0e09060601140c0c01080a09060603121106090606040c030225020f0609 72
    0x20080b60404001120f44040d0403010ba1600c8858000410002c64003160350004141481001900030180c40c0c002c0780a0145050a402c260b021314000800c012003683d450703e00c03100d4441801501d040983c1c1c0c1d1039403820a0303803036030030140c000300c0c00020481d904000780a42e110702c01da41d060420410b0f090610060840105002d18401902d1030004101595503050200c403044440588041d050140120141d03207031300003500d0311071005c0310008004036924000c5003580ea000291140662100c202600111141203000d0000d850721444e050b00881c54400491209101e003200c0300052180d810440001006400036503c2813051600c2401106134460000c2594540c400c02444d107009140c40350300400c00100311640b0010b100510340080042001109094200048900d40b5020502c88100d0300594440d44111070f880590740005000681c00d01d032a51043d000c940b4145801428540340600303410318503242c0c0e00c0d1a22450788160000045107070400c100503c410b03041d1460307800c10700488040751b84920b003402c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 157860062 1250 157858812 157858823
    0x1b080a030e01270503011d1f02070b04030801080715050d0b01020f03070c050a050604050306040b0901090b070c020901080102090a0b0c03070203070b0c06090102030c090d02180106050a0e040e0a 85
    0x1a540a180c0c0c80f98107640100441200c2c8109005018202e10324218164440d02e1300950819040b000d10f041224601d04210307090700c001e0980c0c0c400082c1c03105009548030381000c1d003050307081c4440340100d03040b4080d0603c1a0701c40d4407450a41e5040109103450022164030001405101d98034216103da441802e4a69900c1c0344100421801e0035080140d08100b03014690004a01c0301241c00014410403043c1c07441103e03819601503090903140c00a20056100c0c1c5d01420f83c1550083d40898000351a9200307507940142c0042c00061195000c0d40d611240314410344a1800040032009500c040d484d100301c0c1c65006020680c000c6181a51940202e000c0803064072608400f84004a0140c003d10b8091080b2001d0550017401d880d00140c03a140010345d960401c10392005d003032088000082c51144144200c3c3c1c024a0000409401c00c4942010480c8982c071008049070000c202c03c5100c4074801c005015a40a000c2036242c86860720403000000382201d18589c0940c0c4a5400e0030300c5505404804a02204801e4104 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 157861312 1250 157860062 157860077
    0x506070c0312140d0c031805120a0507060903050405030f0105160c17040b04031704030201091403011b2106030b062709030a090501020a020f040b0a030b0c071b080a03 73
    0x50700d040c0d0b01c240d0f0038440d500060f08002244603500d0315690000660b008192002c0082840c81c02580509000414004000ba4000c52490b10400342c820023501da901c50614005103424400d83d100c009440c20700b60210f010070b101103400e2041e441d00b804000f034480d210384020031881ca000358120b81072181c44840e00c000e2101d081c2900051000080c070940440021185a81c2d9466407034442d180285d00c90312007075442c0c8031514808280e0f51030301c40484d8101c9405a40c0d100c40942420111a282000c02c000580c1c190b607035080b20300b401d18500400c401c0f4101c458a640d0794100b0b80300341013840e038042c901300500c45600d003040610005a0001160b5003000081c0c40390b4440540165445081c4900e40007a00d034020b020384100040d03034a0000060103050340c0e41d40c400e2015555500160b03581e0b01c6200c4001d6002a00c80c280340c0d820f09107a44501c035607900c02018512946d65a40303450040380c4054070251481d41000602c40107002d035407420346a00c0124401481280c61400468035250940501c0040030060318 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 157862562 1250 157861312 157861343
    0x402040b0f0301142a09060d0605040c0c0213060e151206040f0302150105010c1b0513060e0c04050108040b04030e0a06020d030501061b0b0a1d060703060506070c03 72
    0x140300006407001000390081019039005940b8903001e0004480d00354080003100000000c41201e00303610021541564441401c280300b04003040f001c2d0300101c2440501994441000078243c0d00c50041e52640d08607034503400b05403860f5005020f160070f035800303401d114181004410880003904036441d43d0f000c8528840c0f4500d5410400000d800c86a49946009903481034000b07100030702044d480079282c4a4440e400b01c6d01c0715140302c2aa840344540921031680812140e01c07412010991a4a0288408d01d038100b50784240c40d195400207132100004a9414490340c1e07964024840703c0540030606030005a00c084031801d040c54000000c10089000708010b01e52040300c0041820140507514000c0290700041405401d00d4071908000d558640103420440043c1c10800000b401c01d000c6c15a16a4044000540c60b8840109440b03c45050f0400b4000e20696580c80600d20101c02e2040312241d4240070b98006812203080510000302a18904d4020342c0c4608002c0200703000062000c1d81e05000c40e0340c005190149440c8 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 157863812 1250 157862562 157862569
    0x181c06021315050a030e0c0117060424051804020907120b04050a0203160f05040611070e0709030311060609040f0305190f021b060a1809020c070e0c0c060402040b 71
    0x107150b40310300180c480200c001c0880640001c0500040d9440395401c014100000441c0c9540c1d41a084101d0701040480340e040032294140d0814503444400070b400841c0301c000042140010a1700d481c224407005a0001c03060001e8038080b401010898208000300e1040d081c00c0d000500784100c050b00b0481480f101410703410420000350401c14031240000e00c03c001914226100401039030003140d48900354103408690541003405460700b010000d54035922203090500342101031300c1c12040b441c0f04161501c07510340c002900c54105210b00c1e00c609107a42d116000785255103005401e414141c80011142d07040780382007244a407074681c0100d51254024050314417950f468201501ca40c410700340d641d680b002114916103101c58100c20710f8001080c9980c225120001c5143c3c41c0c6e44031701c40322030005034040000c100240d0b500384a42c80010804042c84400d01180c0d56501d1184102d9001c152107111582100a0030440d480a41e0b074090341c0300f4800344815180840910780c03646c445900030300081c0708640c0c5140d190415107 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 157865062 1250 157863812 157863847
    0x1030b0f060a03140309040506240a050702030f0304080706020d1e0905040218030c01030e0303061314011e051203070f050705180a0b0f010504032004050705181c0602 73
    0x113401800d004e024a0412000c40e0310ba0380310a05e007038022828080840d0039810305000d9010101d44085580000085111654803198441015581000003e0000c4c2c1e000d0f07581032007515402402c40300216039562a040c501810140158091000c0d07400c4000602d21554010640401c00c9036a00e005005d00000c281c1c050b100070800c0d81100d0740151000c210003010224458040e480410120304440c00898210011020760308102c800c2d00c25034206101042c80d81c207101c180888400300da0440868440c0d10607a0480d0381e280e0903440100144124500e1620f0300f400c011105000d000c2c10740d03d0040381710f1118981607403440342840090140340500e405609001003401000040c0500074000780f16034203c0a0b125221200c1500c04030201454a9841126450300c61040415440182c482c04e092a02d95112148601c031002e411030f01003c0c4d5614612115515031140034402c030815140c072912614070b070540280d40100702c42ea0500840b40300280440050742d00040c04407550b401040540d072200e8030701e050011f50 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 157866312 1250 157865062 157865069
    0x50307050715090303110f2b0e030316031404030804061409010b120a0c0512010228110604031e0207050d080309100501140103050c1216120501030b0f060a 68
    0x9840b00c120360951500d6086a465540250360500426001580410301803054250f04803800200301300344900035501609507030f00c001014101d000d5640640b80020241c80c0f4040017116035820002c02c0040c54080061040306a40c190300e410040d202407030004024801e400b8002070305000940001038100318441d0031546086c10304030140c0025007411081d143c06880303a0604070340701b0800080e078009511400503030002c0e1190010281980e00d40340005000e18001443d00b4801d465408000c1a5058000b081805182c0010045942c0741240717002401070095060101c035032540c0e0080c200740404603900c2440301d0180114616074625080010a0591810340345501c0b003500032000d07207542030601200d08007561244010380c050351890582c145990080b10b00074022400080311110424803a94442c0c2e00c003a03841001c0300c4440d031a2420094250f0ba82d10f004a402c914003140d0715180402c0382e80c0c041101e0074074400c1010306000d1541155120160350000031b0055150044800000f20385603122600003004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 157867562 1250 157866312 157866323
    0x3020901050d0519030207080106060e030d050c0f2b02030901120b0109031509050c03030c0a030c020103141f08030f090409031e0f031104140f01050d0e03030906060a030c060503070507 81
    0x2e4013224607002e91250380500c505140780d4a400c4001a029016407104050094020040d00a03041c1c0800180c0d02030f00107107034000d0140701c1c025040004420400c40c180d07621856060518841d8058002c03241c2c045064507888085410500c0b02807040c0e40c01c0903050f4036a06455a0201d0b07038094900040320000160782c03028001d0790010050801384800e0340d1000318070303074064000e44288000000905603a4400d8003034000056001906201c0840d1182252160f104d10500d004100c1402c0101e03c0ca0031241d081d24900c0d69040c45500400d030f00c503d820b00c068003c2180c28055401d0a0394405500901e01954010364001e5854503481002c0510644011000a2100070000381c0242842c00003484c0c1c40d0b1503407180c00482c0c0380064108c0a05c07410020388017180c0c15002c5950500141805000b5001070f00c40e4001e06100c0c1c00d06c41c0b021040038a007d0f41d40043d9282004540300c0ca000d50f0a940b40c070760b011b84498016161700d0400e00228030881d600809076512420100d40d00d0306c801d54121018400c44030054078 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 157868812 1250 157867562 157867603
    0x4020301020d0c110709150621020c010e010e0d121a040504050303010303090b04180c14041205160b0f1b101e05090c0d08040e130c0b030103020901050d05 68
    0x2001034000d080005a6907802e01100d4045d510381c6802e130704443c269445001c80c107a01080800910f840356074401c00300c030050602054005078441301c01060360412680203103681d448600d11928104240f0070b20f800d1031070540c000d0014020102d400303083c001a0710408420242c84100e03248041c0080c00181c102c0d150b01400402140c98a81820303601c0785c00c02e002c02c80000305d00260014440c180c103805d85041d10400000c2d642c80d075150380270400003050f50288070300c103000050030003440c02a0b075800900000c150401002540340003c0c0740c000e081c150783e20b02d040380741d4140c1d00c8203000c842185003d60b0b4010440c091000d070307503c0100008412010600054240500c00c641780103d500300c0c42d411455803021494843c00440e807511a40400707964040380c0c0c00029501c00640d007141072809280321011540a00c2d402ca2410b134079000114007000b070031a0041e09126003800c00d481005640c21020008051080019080d5411580060400381040c406c46114185034502c10080c048240591118080500507540 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 157870062 1250 157868812 157868831
    0x140c0a15050906130218180a03050a111605010e0d06050408040608090c0f0405130b010905010510140a050f0d0507020a0308180a0f1a0c040306180f030804020301020d 73
    0x4001d04030440d03268074140035880100f1390a10729403e50445031a8000c0222420598140d100c2124050080c07080200411220000c2454003003407100b5140b09000350b032110b65501100e10090b000700703020480c0b204107030b0002c15044030b0460403130010001c2c0c5100741fa00f45403c0e00d2060002c0c0141c0f400c4840504264500b1060000b00034004004100300c941d55100c1c0c049960351941d0107510f81c2000c9045540140c00b03d070040c161498290f000c03075031002c281c20181c44000c81c2c1c0d8440701c1d0200f4098000c91129035803000180514034000c2c004e070642d201c1a291515001aa0248800b00e40c020503101c103040c4000071501c1d01588082c0c409440ca8402d201108011a141030180203503181110541a0040381c0902e0109081c50b0440292a40040c1c1c0540140070810040e0383e148455011108144c488104094015144410008440c3d0294000d0044140c0380d50840c01c0102c211002074086004028059804034001110031540810780f03601401c00140d42d035558000300e40644514401000d60500c4d14035150b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 157871312 1250 157870062 157870103
    0x210090506040b0d1808030f040312090f05070503070503120a020c1f030f020c0a0b041406010312020708060f06040203090703062405040608030f030415060315140601140c0a 76
    0x41c1342c1428003c82c180592501c03490035200d12040010302030300b0300703000b0800648610404080f2a40052081c640100b102800c030400c5011901005402c42c2c080d241800001c050000400c421009010201d025246051804000980d200d4003201407a465060200760340c03446c10700070b0020001008016003000125804000b8002103011038445503404a440e00f00c840c4903d08561090f2003900000300c1c002c00701040541c5a80a980d00300038012a40005c800e1220201101c090120034000c40c0318020981170741c80c0c0e0000c0a420954103070006589940a841000074101a10680580090094a00682c0c03515070558060606ca0242c101504960810010424011a100c500c0100c214440e0811203c070b40c949040005542c1d00b032149a0b07680c0c5c420b000740080012544020744d001445032100488928810640c44141c9450390300540316580c521480c100c900d001400341602190300d5800b8a80149411000a056000c644103201d00e100801b00d030720720040d01d0810a51889a40106005910001d0715420 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 157872562 1250 157871312 157871317
    0x9091c0305040605070e060a1206050613080708120423031f11040b030c130905090106050103110304021f020f030c070303091505030f0a02040522150e01030210090506040b 75
    0x454400313240800140100c0c2c880d030017611400800034102c0c4c1c500100ca0f44212034044c1d40080900381c180e42c904000940e80d440f1001400800300d080700300740e92549040d04460034900140d100c4002500a820b14114258540e42103c0c2591041c0c50014541c11040c04c50a107010b1071503000d107806100d070381c505145942e1103030614100300381c0c900c2c0c040c4018040b03051031041c18011485880b025030340038070128a40d03000c0030018002050100990b01a002e5803105280700b82e50701612500c8035659540418066944d16002d00b5201481402e1a00d266050540c0403a500002403400740f02c4070200c044000b0310940c824000940c90030a42000c49444000c03401e1700035102c01407032104502090008000003240f4042d2580010348869a44175030b03095980b030a82c1034000440081000c1304256080001045030366503038413800346214106007000e298641c01e1020200b21076241342011140b80030070408220328420030503142c0c1903e0f07040c1c1d41c9042d00156620162080c80c115000310341e01840103c1c0200c0d500f80e03007501 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 157873812 1250 157872562 157872571
    0x80307050c1c02090f060301020c0a08070224121803070c1d010305250f060201090209250e0613060f08010b040b0304030516080d14090601050d0209091c0305 69
    0x24a820302d02201c00c1c0c101054081104001d41008940300003505c1c241e44405d60541c00381002c1c0c0007600d4403401071032003400c5c4480c2034001c40300b110300803030421700b5030500e4401c10304045102d821411140007100c020307050a010b501151000d414600d4009680c40c40c006441d0410040e64034100c1c2e0300c40082c0d00c4d1541d40e40005000c0d0401c0120f48040342c03d481a840356001d412a50008050b04156031800b860030200d4100110044e442240580700140c0000c0310300001c0c00900066000040030720451040000401015108082c0c264520071400403040c0041032043c0104c0c480c0c24036209034041c1e50081038003801043c0c600d050305401914001010780d085805c645080c0c000703a0b034940042e80c95003414691405030b4003d140d50642c05000250009000703a00030514812140c2035140b1501c410382d06c00c0440c1d4094082202c0c50b9854110070020390101a80c5d09400c011800003410301036040a001c0362644428800180c800c81029010868000091102402035030341d80c06010b4003c0d40251014018103070554 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 157875062 1250 157873812 157873819
    0x1709012d03140709030201180503060a14060d030207050f010e040905010605011103030114120a0c08010204090c1e1803050607030b100305060a09020a030608060112260f0310080307050c 81
    0xe111003410070803003410511800190f2100481380c1d0035500115101c0541c5500f00410010320180411955030410480b441541e4800d8080f540004003090084c19004c0540180d0186540d21522000650007180d0071040e90300988480301070810300001214090300c1100100c1d00145420519014482c042d003000090b0342c5c0a807210b0b10094182100d503642c03440244183d941500040460081d54940b25004040e440106401c0b100030b83e03c1c640381c00304040196031000f8650b0394000f900304240e50260160a44440751401d01d0070000c4140e074001110180d0301d42120307003000410b89943c034984003c0c4980d10003440d00070040b240b5906c1c143c1c4016006100f4164480d00c55036100c0700c42403125100e8000c16124220142144043c6440c000d1108080c0d040440303c50f060603100c510114042c1800c00c0298024100392200744004d03125030500b001c0741403910980d011545248034800d14010099400c41d41701ca001ca15401c4e0f070320740e128041130580c5c414a4118aa041c000002c558040c0800040c44918020f8102c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 157876312 1250 157875062 157875071
    0x30403230d1805010c020d02030d0801050f12030f0904061802030a06090c02150907120812010b0a02191b030605100b03161b020a0b03010e0a0204031709012d03 70
    0x8071401c0c0e807000320140088264032004031040c80b455101d00c0e680300801748041d0509120700290380c00603041c0300c581d003000000100c07088010816443c2140d20081021001e4500f29464200560155180d205d620048410b2010000302064261160b40c02a00185050142120400766190b03c00001c2e50055074002c2d1968100040420740707030180d01c50340300181c2c016001418031260794010750a041c1801030250b1440e01610a001072000b4a10707100703c40c01c80c416040700c2d550f404071000300080040180c000c0c44a060f41405001e01c0307e40c0010b412480001403d10b40803103284245840721501401c100200f01164464000104021451b0440760084030710841d40c0081507180c20040545000c126108428041121140a2800d0150382c90009003220300a00c4142582c41e50081034401030b5036446003031100300010040003100e007134125a50300304a2100065180c180340d17482d8000007070b42c90110004403a1000410540c0307a030040e00048006423142e603642c0c0c0d401021012141205e00422200310200b400c2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 157877562 1250 157876312 157876333
    0xd0e010614010f090510030c26060d05030d0204060f0e030c060d0e0c0d08091908070302060a021504080c010b04020301050604090203060d080c0109030e010f021b0303040323 76
    0x40c0520010740d8015648002a4818580119908a0500c02c0300c418480d40260101d01601d900c0c690940c150342a440129407c000420020004100e11583c440c00710900710070340b2083c5110311040f50700544110358926240500e0309281d82507105440303444008500c002400140240c21080ca8883c0031003a0f19401a000110800c0c541ca545a28410583c42081041031500000c0f10341d10110020000000702ea003800c0a48012a1315004584026280c1002c04515481d0b01c0c60203464151241180d034101c512407501d80758015566100034000248038440204001103a82e03c03c00c8690148005204191203500309403c08004a60215000300c43d80e5081019100e400d09140c002c4034105c403c003408251500e45450074070700094001609c001d92161f110300680c00800e400401801d0204002e80000a0111144c80d002d020b030540700c50058107100403034000321052a00480c00e654000c0b40b03900800c1c2c40100ca4800a030541c07089410090010710381c1720500c006c0707068524036010140150000c9800b640744 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 157878812 1250 157877562 157877591
    0x70311060712080a0603060608060a1b020607030209131407080a151208040806041109060d020d0605042607050705010305090703080c03070803090a0b1b12040203031207050d 76
    0x42103809440000601d0038801c1d82c1d80b2a1290030380c081400a00041e020361640c2c3c0e100195801c90703001c01c003903a0101c001d0000251803441548511145080c58554406269001070b489205c01804031081c56404140c03003d49485000501c03034240e007280000c04c40240c02c80b1000b80302410655080001504010001c0c0e6136520764410b01c040b120703a590b04000c04524001602c2d1201d84020701c1100c07e00e0b014000020382802c10402c080c040c612950304206428a0f01c400e10554100c02000c00c3c2c8904c3cdd44218540140e1a10640003600d540c0001003c25032340d8a6040040680a42021502c0348113030b495141c107100c03400c0740c02900c4114403403000e5130461559080110b041c1c40c400d94001d055600200c034108005084940145003840d0010700307890a0003841d45440b4400e41080765400e00a4100e89010000c010381045110703401000003022041c02001c0d208040d000d07020385180261006a180045401d554081003552031116100d01d80f018207142000c0c0003070541e044030070b080c00001d0800380700519403c03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 157880062 1250 157878812 157878817
    0x7050f0d030218240c0a110d030801060c05120c16090605011b060b0d08040819030e0f040f0507050910020601030503180d050d020d090506040302030607030c0210060807031106 77
    0x80301d038800348040e0400758040000a05801907400304d40708882e21803400f031003c544040c10069003088040d11200c9210b0410011400074040a18071031603031140f0040019820080141c15243c180c42c2c01d4101202c01c0c0380c658a8820100040b29080d18046010a00340e00b000550340b0302c0c4403440001d42e190f20381d5215020195a198040d8a0120305500e00c402c0c80400d030b504450003954080c44010a81048500100d0f641801d4040700b5600d14034000b4061155910410042d1800101303803050100f401410385000300910001590303144500381c084041c0c900c0f17580d20b82010b00310314403480c81006203042145000c0c180303034042010a4002c060084014060700e0011404a04070703600f207400b540c54196210f02a90311905581c030010b500403540d800c04004070b102080349900740040c1d500102807030310071148050542040d60f40314034420b8004100c1800142c42c04110182c0181c0780307040c003084030720444c0016070804441300500a4070919010000444035000900c002c102c1e070150032100c2c840318210082c4a4a031 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 157881312 1250 157880062 157880077
    0x2070821150414040305030921040e010e190b04110f0706140f07081b130f05100c080c0a15140a140402010c08160602041e0303091802040b07050f0d0302 67
    0x90070f03041e00107004203002e04010b550005100d0242c4d00c0390003500840c41d40d0034052403040d968800003c102400441501c401c1c49001d0b04442d56025218a4440c1440014011541605c0350305078172450007a4954440c4d810142504e22407031845500d681550801c01c04030740041c4800d441160612424034981c0c415180d183d0f008803540c8800e03030120340c0c844c00161400e40004c0d2840740da01581740241e01240c84e001010300412064030b120743e2003562030f244414100800d6078016038417420301f040d0003078803081d0000d5415001d0743d844504151102d020b484424108007030380c40043c08818030f01582c901c0c24011507100c00190911408030000c152100c402240480e003210b110b0051880d1448003044c09903020f00c3d4140c0070701e403043c020145084128800040c501c50380070021a10300d03401060078000c1c202c8240031410340300020680c65022526648005000703a40c54440e280f954021210781d162843f01c6601110080e0105040c020313511945c502e40140d0f6510302c0c0c01d074079110340980c5480d041214428001c44e43c0702c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 157882562 1250 157881312 157881341
    0x30010609051608100e0c0904020313051e0c0d05031b03120106090f170705030d0f110607020607082517061906110c0a06020c090703110d020708211504 66
    0x2981004d450f400c102d41d0160280c54407074424041f0032100c0d540e500095209000440b6001422400d0f031038264038041c040450711610300c180030116001a0f00c0040ea00d2561101100d00440e0030019090890441c4590b0710781d0105240741d00c0c3c02801c0c4543c000010000605401485804c2d80e070b070740800312401407603400340f2204603514038410031000c0c81d000d1308804425034030070170365403030703590f1040064039002030540c0031030100700b0100ba144a107a0b0890300084480f034101010740024505840004c0d11524004c0c1001e06014140010801d00b20800300c0407a408030f45c0152950014000b20405058003818104100030030b4000c20021301507081008800305480380144142c1455810000142c0b400c9007010030700d0b9154800d500b910704080d80c0f00003001006040c20b8015055861b51102400700350b8030010075540516007821540640d00c1c0040d000c5072a2024030380300041c0c4420346440c10410750720814501c0740204140d51007000d20514000d01e0980514418401d00700120740f81c0c01413109842101c0d034000b49 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 157883812 1250 157882562 157882591
    0x30501080d0507061401060809010c05120a180c06032c0709020a2102090307051210180203010f0b04180804140f0904060903080705070230010609051608 67
    0x2612400740d0090960644180713008130340b4020f45040080003800903484680018040414800c040e5000c3c810104450424074120b40381101c034080081180d00b006e0104660130b035640340c440a10714034400000e203030158881110018a5903620005016004d030020644503010300c01032441c070322003480a40d950b01100c48006007111901e40401c070f900940203201000e00b8450041c08402014100300250032000c03c2040c0010785440080c0c062510b8000b450b00f080e402040c5003400c4032040c4c1e10001c1c0789901e42c0c202c60804124051074a104405031b84201d0402905503080640700c1c01c807204581c02c00e1071000703000e480070880f40e02d10048806509100e00c40141440d80104414800145030b1014012419805060100304410a00209210711003c42e01603410507039542401e0200350b03001504503081501494501d0510420750000340804851450b00001010003544400500741c0340118085189112002045001c1c2d694410031b0141104440c2540180c0040c000450003c0c003a40c03c07030b030080f0843c101e0b400c07 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 157885062 1250 157883812 157883833
    0x10503062a04090f050105060a05040b0c150f04061b090902180303040602060103062f0a0c020a170606030304030c120302030405100c140615010528081603050108 71
    0x514210303120000c07454014502a090540d40a100080000b8200030500088901d5050942d000310740d41070300181d20403074041000c150010350150942c2c0075030b508000041d50f02c014040d101c4c3c0c036245a400040218120207000c2200310503400070b000e4803c9015503414040006548405203018503030f200d0420204806031024003082601da40a42a4100c2c001c000c400e880e0b10250029146400c01d910030001030780084018000c0000c03602900741c60301c18269004196102e0074040c80c401000c0740011149a1002081e080c01e107030301c12004078044640241c40758051a40300d070f01c0c41000d10450031801c1c030640308450220300d450600008a0f001c8a03040328084079030740d040c030082048801d00e0000c00c0c1c00310700c400d11001c5000d5036008210000480039890f8054003442601c0c0c101750080402a070000c01d500307c0300170071030365a080342c903e4030041c0303801d00c2c140d80c1d1850348600c4190080c4500003a16210941c1c415010291340d04a06406e016500b6440140000245014110280c40e424000e14945400450048 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 157886312 1250 157885062 157885081
    0x4050124020c092e080115060e010519020c0d08030601091d06010806060408010f15152f030d020301030311060709030201080a0204080607020a021201090503041703190e031501050306 80
    0x554240c80942c480381000b2040d8150300304c2460b1581040504da5900c04e0780c0b103031880800310381500900503810904c0011080c80c001030698010221020005114220b00c410964801d001c5040301c080020001040d0a005040030701050700700b10303100c1e40407813010400030401013904d00703614601a54403018407005507110401140c82c2440030f04601d411030018040407908103001e0145080c040020b41c00040e010181e15008400d041165001d031001000c1300c00a05c00c4980d01c03d00362903d0150004088101d0a02c2e004105505082c1000347d961074080421100818081500198120380c0a41c0c0c454403c4080814010f4640e0402d440c280045603030790004000550203003804d91303402070420304014206580c0e88843c9040400840c0c2060058009000f481c0852400c00d224131041400d490003000107904954449650744190b004000c00700089100082e82d1540030001c0b200d102c4462841980c0803910602c0191440705940e0015109006140c410142005403580e900d040750002801400c240d1521a00c9 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 157887562 1250 157886312 157886341
    0x1020a0803181e010b040b06030105010c1103120403030509030c01052814040303020d021005091e01060f030503030a140606030a050a06030506270d02062404050124020c09 75
    0x600a0b03402003a1070820545460142c0c00c40f0f5851041c00410520389420401084031529076115204100038401070040b07036807000c103070b00b0300540c4000301c00300458034000000d1030420302c52294001070780002070200030507600030054140c2e020103504442080c020480103484034081d241e4800b1098081014611065650603807800450b40c1301d0070812504403640451174420741c8984c2050f030145e48800002c003070895040009402004403030700d08004908245441079111040d80020741c0100c581c4940840503040e086d4807d800030700e0702d4008103049507581d05e007140e00c81d00100c44e6980940d1400100e0030f080195483e91912503d4001e150f1842c40d070b6a5404000244805000048450798600340403000850410410340940d89041e403220441700d98450845140c4051550328640c1c2e00100600042c003900080c1868002031801c41c100d11140860b0044910034550507107441d0304c54107000c0000f6030100c40100b10410346245610744403004504020903642d0303030094090250408200400a044030107403412 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 157888812 1250 157887562 157887601
    0x60e010e0316081c0605030606031c1d03030a0f081605070b0705190306140a120b0403020f060703050402010f020c01020a06021e07080942040801021603020105010501020a0803 77
    0x183d241481181c0b018601da1074540440c02801c10b81d502824006480c0c10800c00d54041c604070024007a156902c80c000c0d18480a281c0d001b0103204040405004203841858020741d0880b01a0803070b601e880300218002d1101407480402d40129100a022030509044144802c0006942c0e4603034a1500c295aa0340310880100206400100801030041074405007d03840038003103000c510341c2d0108181e401d10180e03042013500e00300031a1207495080c2c2e04200c4000c00e4105806025080704940d0352550321030405908082100440c041103004d400708020071244c06500c0350380110b0007039075082c5043c0d410f5003040c3e90751010006818050381c00700d5030f900001202c0f5001050181e401d10562072078118140c185007036a803c80d44080729a1880031451446078140301c4a415030b40010200c81c409400100120f40807a9070400680f00541300d40790f02e148000380c0b084000c8800a0440000856590040c0c00f007640740b880800320200c0055080c14000a419840001d2101c0c0058101002502d941c5400c11520b1152000c2381 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 157890062 1250 157888812 157888823
    0x10f0608060a05100810060504030506040b06040207020d05010e070614030a05070311040e01030b060402071713051e1014090103020702030a0606060c120207120201080402030a080a0c060e010e0316 86
    0x10200f101c0d1949000380c111490580c42d0041103041071520b5558641c0c06402010801000b80010000b14000090741ca4201d904084004800d48918002c00d0192050f010302035000441d10f40090304011b8151322007080e01c060542a1089070b40c9420003101e1200311200703a400305000034808900000c40f00d5016580000150600140500c0500c484241c2d64016900506220485200410078007103600d01032680104204c50031494495256100f04a07020a500200da8100b4040740d540e000884110700d44000e454014001000c074030300010040c021620080b0624000d0801590000c07403540078000102038110019038045c281091800110001d40100701c040c0d90606c180c182e540c0c0482c0492040501034000d0b5034407000d1030714003410101c0307040002c8400315085501c045c07001c000c0c916440c00501c40d8180d0900e0418515195030001a140118002024160400000c3e0804803281c01c2083e00e10340c944142c000340002d210100d1032070308030790801035a0300e0030760407c01c80c0318032410105054039662803241 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 157891312 1250 157890062 157890079
    0x901090c1527050307050a030f0f030c05070f050102011d0c010e210303012103090501030f0f0e03220305030d1e0204321509030c04050c130e010f060806 67
    0x1030b05001c8249076003040030000c4155140c001d11440c20144204006003109442c00c2d421545555603082c1000a00007014004e030034101c400c2c0c4c041501c2280741e03610701c0390040100c0e0145600c440c1d1a5400040c1845070074003542c17a22400c02140d4130301c090300e820302000000c06810000d01c41401500c0b99849410015808017986505009c0c04072045683d6185e00340c403000451f103940c10140252422039403a8400c101d900c484c16400300000e5404400342040d9642031902003010700f110703d0303030001030803249001c40302c5030303040090604034244004007038540d001c140d1f05a003200c121210740304104080940400342c410b8008012050103c1c015400180c24840305018107070011024518040490b001508540504201800c5e40341601286a000c0c242041d81514011141c0f00100001050005080032000b49500e02151040183e074080c400101d40b41b10140041c0814a0007180650042e481a01c1002c00d0301c1c407192022411010b0444014165200440d40c0c082150038000140c0d6440700c010440c50380400702 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 157892562 1250 157891312 157891337
    0xe0f0418050102030a050403080c07120e01030b041b08011509030b0705041203080a0f0b030d0e01032717030c0f070c0f080f060708150607080714030c060901090c15 72
    0x740700a6100721780c1840d0001e010700b400e280060829501420740c1203d40010f01040c00450464402c4122081c0d10341440c0c442051418010b8000d40031005649138020b241c10740c500c260414040102c00345210660352030381581e0301d41030b0010242c8041c022600018443e03035400d1002820604049030405240d0410038245540d07032010304a45210440200c0018042e00144031580b60a03024603c500300d041c100501102c1860808a5030302d001203284101040404ca109a88503402035200115403250014800c1c078664900c401280007018901088414844841c24440c45103c9030058900400d0b8841c101031034604020000c150f01c1d00000307802e4900b18060180000e203d80e158218800900070500a013418450005440b420500014504401d0041c42010040110050301c98000407a40c201c8109442d141141801c80d6a4050b400000742003240240501d00310302d1001002e001c1d22000c90040318196030f1810b00013403e0f21081803006000c00d13413015080c8050840c400d01810b420020385001c2c0e00001e170 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 157893812 1250 157892562 157892573
    0xe0d0606080619050717040f060905010f0c11010c0905090411090f04150603080904020a0311041716030206030402060f070f11040c02070e04120c0606060203040f060e0f0418 76
    0x4059644101d00c1c0000c0b00320069854482c00b445501c01014102110146c40d0034042d010040c000034001080b64040410b16000c211003036102c100e43c1d41c1c11600812000000c02072000003000d00342a4080071030720328500099007250500403106102d03029610082594900000e1101c4100080c0041380c2d9500704a0141f28240c03603642003070344a650b69400341200e509207420080c607040324005001da074182c00c105041c004114051b00700c0e030020406880040c5da80340d0b010382c00c50042000d45200042e40ea400107000803c88181d52003010301f088030105403031102e440340140814000d113901c0000d41028040c0002400b528180c005012002e294900c1245003946607590f0b2154041103403802c4911380c42403101100ea42c1031038442c800002c03256000a04c0c0c85410300d0052200c80f40020002401c00c02d0320840c4070701041c421051414801c0d40050e0910010703458041c003075141c0d0440c1c014280700a51481d800524188100000c418540e005081940c4e00c0707a6101c180009009988a284100d90610602400199 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 157895062 1250 157893812 157893823
    0x330c020d150209010e0402071110021e0a020111150103030f0c05100f270f051207060c0206100302060d0b041e0504021215130213020403052104060e0d060608 69
    0x7a00080042e6500b1541c40090004c072504d040c114052481401120001044602103005c0c01c0e404440b4a1040641c1d600100c0c0707000b0000c0f150320115684085048206400001c00c080d055100340c8410320306403c000c0205940d4002e14000144003401c110040011a0048160030000c105a2070100f0714211552180c5203090301c12003401140c50760302c003410300341c0100034810700f6115600014040300809101c42400078205001c64051b1611249910b942c08205c0c040111030001031180d5100c9460381c1860512100034592031003c1c40242c012070001030218000b80040d281501d50003045581402c00d5081000300401b01040381940195881e040c440c0d500c007a409402d51000a10032020800b40752510510502c00091041c2c1e2500703034020380690401c104514106c40c0c0c0407214483c0c40100581900009941e414041c9080204d00d10001e07010060200100302003404000da146916040010a030300c480f0705100d144035100015803c0038030351200c1c0c5050404405600d010302c1020a03c0c0f521543c0250420 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 157896312 1250 157895062 157895093
    0x100507080f0a11010b0105030108030403060e010e0d1107060306120b0a0b130b0307213e0315040201020601150905030d05030702120415050304050f1501330c020d 71
    0x7803c5040b025400003024010b90400304d0f804e20788281994500308505a881c002c0b40802410951103c1d01a001650300350310000d0254120022074140c01d20b03501010b4000341c0000035480450091031400b00310f080c007074001c5000b12541c00c24240340d50030780d503281c118000c40047e08482286e500c6500030b903101d5580b440e141d801083c40c403030005502c0c0320380380030140f0b420115440441d400180b0305202003400c525040d00750000707400c141d0440310903a01c240900022940300d4040c60b54506000e0701480884044500c80310700480070380c1100c000704414131407060281400ca40090050b40190010311180d21444040d00e8030481a0030020f200d01d0711040000e041c2806010704100154000c0b0811120301c3d4104841955040b00d402c40030b18003070178100200c5011411102403000c0c050000045400c00c401000280c01c031188403811781e00340910768084400550b40030700c242c0490a60182885480030300c4c40b0020740c01c0304032861707030400c1e24034050005554004400c80107a03408100440c843c000300e01006201d80d42d2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 157897562 1250 157896312 157896317
    0x7030b0a06090521060a020a0504030b100513022a0a0b160e10050d090f0b04050708101103011e08060c030901051303021011040801060e0105041a100507080f0a 70
    0x1043c200400d1001e190f02c1e1341d070b20816000c1d41ea078240c10010408520507800c01101c20300542e036041004401d4840d40310301d5000802400b0901c0802100c690280c0c10a000d0322000c8910313880c10540c9074485000c2e03005000360f441c04250299000b000c88e00000191083c844440b0040c2c4903581000c0d00c0e08805e6110880325218448003603246440c3d40e5502c84403480340d09004a402c9001e0600c080d03c020618000c00e40004070495492780010b05102c4800308940c00190700904980d03007440c1910b41552140da05100721281849891400c1c1d440701e00d140a4805806103d40e0110700316031802003010340c1711004001c0c1030401d03040c000300070500c04828400c86105481c1020000e950b804c0c02442c06003110340c000c0400c9410303102481ca5000107580480d9108040c600304902103440c82c10415031070b056110f41c0e80140003640c40d0000c0040c1204218160a040741c1044808028000d28440b03046c046032410317440140e002042ca18112001c2d40a00054842c481c01440703810300b44428031038100055442080450301 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 157898812 1250 157897562 157897577
    0x180a15050304120206100e070e09010b070b0f061509040b0402070b0106090b130e0601120c030b0f040911121606110c040608030307200102030c0a0810050a030b07030b0a06 75
    0x81c840607000c0c0b6443e0040c0c620041c189450705403049076180c0818052450b0080c03144021038541446a04000d60f5108000c040180700d583d40e68180700c0c558000780c0115050310710300d000201c04070000d9200a115200103410b2b23600368401e0414450741d40d88280b82c06548240da40300420003d8860b4800f0b49521481104112110f5045c540040c0051500f40c0c444000c4040c10441c024418950400d030382c08072020100501900d846100040e02e00c01139907a00b0720070940c0703458130707100100d64180c200580469090b01c04d1503802e40394405010030b03548402006082e500c081e2400c40d01504041813100000324403a01600c17200b010007441c10100e0304042d8405000034854a42100d00010700740403081402208032000c02400c0d00c2c0420090322800000e00c0c000500006401c1c60340c0d4018031130000d0b034150029000855a901e0590f44d48455034200d074000b4400240c01d03500007107030304e003c120f03011054030001403400d0049440d60f5103200c0081030060100c0300b01350715205015599114403110b4405401d86485000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 157900062 1250 157898812 157898821
    0x91804080403170306060f0c01090b07020106061202090f0f0607060212040b0603060402030c040518010912030507090608041101090b0a0309050105060102010207020a0e06061201060507050c09070203180a150503 92
    0x2942000383d0100401495003c106000780f42d601c005c00c0703400d02c1c00c840740c42e40d40f92007414016500600020382d015128195900422031032070f5043d0701080964945d5190034000000302d0402908900a0a81c55500502d00f6034400001c1d00d00610800d070b01030001029140741c1146d0b030b6610320036130300800c0381900e41240038002c0c0010042242429580b102c400c0e0014600c9140070380000707985014490441f805150790f5000f0410610b440201180000048402404802e07558645038021244070080c64000900e08400f00380c0251090f8508030460702a6a21611240c549803249218842e414040f00d0500c042c402000810180d400082c000c032044903240080d0f40701850421509542c0000e1585045901c100820001680c1d405c442c041902c19543d00d1400a0b60303420003003140c40c0309060045044004100c00003510603401401001640e00c100c05607501030b0955024480840010f4603020b0140c3c03c1030086416848600c90445240c4100030006030340c1d155112441e04510040c4009007000600010402 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 157901312 1250 157900062 157900073
    0xc14120d02300f1b0a0509030d0c05030d020c01021c0c02010c0810030305030a150e1b070305040e1e07030902041503030806100314010e010608101a091804080403 71
    0x25110944800c03a0b00c150361074900b10034a48080c02031401c1000c09035180420112254902c5481c5000030309000e050fa1888111070240254129080c441d2080c4034407a000c480c101e21071a58a44025840002103040402050400001e5001018941e148c1c1d036007807120244038441460410945007000c40c000401c900c013928000d00350b40e50ba04c0b9036420721000100740920025000010360445c0c1d05480d00f282c50b5100d191a0002a041c100404034940d20030103804510700d0310500425016034400d4403402e0301c102c880b20601106009088001d4045441030200700411485000e0b031551045200440214410740e070f40381140c09500680303419000943d910440b90840c117152091103290750b5510b110b00d841900d1550020b004c45030003481d140c0210351a14618501c613010740c1048400e03d08003c6852807940e100c41114011440909c15440040d4225000c03d222444000d0818103480b00041100540620041c00c1901680030001c0b141d0890781072043c884100d644440d40c02d000318400c04003c1d5451f491801c2c030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 157902562 1250 157901312 157901347
    0xc02060328050714070602040b0d0b030714090121020a03060f0f110405010507240504021302190503100f1403160e01141503090105060406090b010c14120d02 69
    0x400c0011860300d01480343d89030b040030360101c45003441c140080e55640719103042c0c00640034643c07141c880910003080d0000c4e426615000090000c00590450748056503410a0791101c0c2504103036260820700740740040c804000c40360108110940c0386404100314414075808604e02030078a41c02510f83c5641c41d907491580035418001c0b440c504d1040001401012000d000740c00c4c00c0c0c41240705190501c40300242034010820040300d107145094561890805d02c400700140c520103401d088400728440c600703501500b031001c1d4092081d5054008a120000044000792109950b65403003e0940c0c0003541030700034001408512480840064201034140041c150b58900074035240907001504500600c901000501c65407040181d103904484103503a550015042c1da2020442e2198011a4800700c020300008020101c801500840e01988095400308001e5030f854100c1c4003103030101585140003514010700300b008078500c0301a80703000c80208400c0d03404181d0885450310780d43c0e105400c90000603402084010032803180044 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 157903812 1250 157902562 157902631
    0x3090503031b070515030c0306040e031c05010e0c03060f0f0406091d1c03050c090d1a06091e100e1e0a050c0406030c1701140a090903050304030804030c020603 70
    0x6030140a5917007040c00c0c03142d0303000041824808190210000b01103070384580005a0403114041540c0d80c400a060703051030032060b0813404c0e401c5d041c10b140c0001501c11007040304c1807003014802106829070301c505042290000203030b0311480e4004203000c1c200c4050784c1c82d8440e2800030480c8400010b41d0604400070481c00c420800210349194008014409055001540a80d03400f1464580090981e445420014040c010340c032138503401c1001c0030880c030108102035120424941c4890300300540c5a507888200b0031641e500b15880c0c507000b581140e03111415000d00000c80d0304803910800006010b0b4889202031000c100844081810381c00880783c8458025040c14810b401102c454010302c15803401e8200d08003103100c0c501c02c40b01010383d40e17441242c560344100d48108107440b41051045c01940c0d00c00c050541c803107250200380c5c03081d418030000207074030082031203200f04e01a4541c85e45d81c00d6585580741690000130080041d4140031a042e00200140d07030317000040d40700e142c140340d01803460451051402d003e8000800c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 157905062 1250 157903812 157903819
    0x7030b01090b01051209030d0501030c080c0a03050c01120b030109030302270a03020105090310051510030e060117120706050a050603060601020c060a05040807091b0203040e0109050403090503031b0705 88
    0x200421150741d001003260313500c0c5000385c058001610f542e1081c80c60761090845481d1118944000407040060b200807a404842c128400c44181a010030100095071710705210080071b0758080e1001c025194001c0b400780d08011400c0b40f00088036036000c004a030a695010302c003140081ea0001e0303400c0d045161030964203d01e8000604041c15892043c022540360520350001906101c4003090094003039404002404561024450a00040c2440704400c450011505001d034455218440b282041602c44d106a40304144400014401a468078a404109010209039682a405484a02c0c5039090383c5800400c40b4510880e4005028984401c0317250480b0006402240b10307400c0700c03061100d5682c1c00100000a108101e6000d82d41e698000380c10785d100e1195a101e40741d00c0c0103c010008525000e80c3c41313900901c1746000030301003019518600326100d108501603101c0d002d4142c00140402113003030340103941c0700b4441c2c2400307201d01e6125000a89103800c10031960708085170705030042d1195079090006c400102000d8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 157906312 1250 157905062 157905071
    0x31b05030a260c03030f040204020712170903130b280c0b06061215030102090a060207030209100f060309020118030b10050603011202042301030c0e072f010f0e07030b0109 75
    0x10b0f05481d45a100140c52003140d0765001011809541e140d070304a82c200369100d01c0c460140910784030090310a00390403602c6900680d41030005800400301104031107002c045400440b911604201c09107605810641d019409206008050742100881700325401078044c11340c50b4500582c5c2c451a142c604204018110f80c020302d4184845c044900f901c450030b9400030801e1142603608030b01040400e009010f0031000030340c0006440800140b1603004240501501d000307443d1611030b81e40d841d03500d0109148078800e4403829050b0343e0f002c00155101e41c1c00003905500c1454412000d01105003210b01c074408941050f00c0344c00600c0140040c2075106601840207000583e107590541d0314011090003040b0050300081d014645406049140c155205c400d007070511400c00e0282035a50b140c1c10714003d0308103075005580c00440110003207200180900040041d101600c95144542d410010558548107680c182c42c840545d29010041d4614500b8010112000c4d56030380149031840c030310b0800404904069010000799480c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 157907562 1250 157906312 157906327
    0x100e0403110d032a0309120e04050a05090d080c040902120601030f05040b15060708040602010c02210910030e0a0302030904110f040905070c050d030c0f1107031b05030a26 75
    0x131000a01d030a59040b451202c4d0400807207000340e0141c80742e82c0004007070081c0004031860454014407507076802071090394100004d0b5210442e50301100d0342503550b561581c2c0800a4042e0032445114020740c0440300807500c070305042c0d8803803064007681c100740c14600041d40300704104a01540d2610803920b40440185045c050b5040580300c002081002404840c0780240d0010a420340761235050455181c07680c40360748039a8503951010024003e20402c1002801409102c0002041c3c3d5005c0c40409182080c000c481880d1502c0c650030001c8600d0300006d800185500c48140c0d500c2c0403404c0c031040704070324000e4000d90f540e00d080c201040100d80e20340c00c10f010340c1442441844600c800c1c0b8803c0e6804d0345c0101e0740000303a54507142e80076204854a44002051482390220204180e41c0c0364101c24010540b585401500580c0d50805075440404030ad0288940da0104000704041402c0500c081064540049030044042c0c03101c02003404e00c0c6102609484002a1000c0300440780c4421010603078014016081e582080c0381e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 157908812 1250 157907562 157907591
    0xb180102070b07111207061410080319090306050403020706020d02070605071b030506040317010605031e1f0f0f0b190f020c040203161211040905100e0403110d03 71
    0x14043d20503000c100703000a07003003407003081005120300d152800302076103848415916000340500381152410320800c3e50310011030340c9002084111030943e19000003645c140b2038448211804000c240b41440c3c1002142d41c40000400d005204940c003d03030095001d40107840c20460040e2900c1c0c0180341100842d440403d0030441315900c4016a010268080c0711003008441d0f000c0e0004001540d030708058054050081840b00301038022008e60014685c0e4103407043c050381d032200f0076940d07404100e44030440860329215501806820f5612943d0000e1006001e40c81180d00780b400300d0b810035590700301041005201d1424014910000c0402004207100c038140c62404400c1d2500c0c0481c542459006028820901d5813004070a000340522000604050230454480ca42286007455148258140101043d00020f88503c8943e00d8052051000102c051540c0f4061408100d10300506008207082800322a404010804075482e83d9617078059402542d581c28030000d850070795411f0010244082c414180752000c540300701768 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 157910062 1250 157908812 157908833
    0x307092105030307110f030f0901050309100204061101050906011409191107031b170a1407110901080a0f03031a030708010609060501030e030f07030c0606030b18010207 74
    0x3000c05100c05a02250040504035120415100800350701001c8200316940780c1c4140101c80d090100d8040716111911007002580b24800c5141249003000104085080c6501500c0110340109000d000ca40d240c3c102c1c2d40006080b03070065040f100000d03504a100205083c4240591a007000602d005040c0d29498150403100840342c01a1090061b0250000203100d80401a040064503400200901000f8403803039440760103070302070003049010900d4501c44694009103200c3d2080e41d581d10140c410001c2200009a403807a8001c0c03600e103010403004103207800403182c401d4080c01c0118403070b00307450103110b082004115a040c016000490540d01030514076022543d85400350004a40501700018408444c401c0c000c03920705800101501031007050b00c00990314030150301040407200480d20800c005910b036001141945e00d208400c02203540144103003c440078040c00102112882410520010501d07607881d00705603602a0f0058640c04a6482001501d500d030881040442e015100214030b0001690741d0035580d10b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 157911312 1250 157910062 157910069
    0x23090c040b010c06060f060f0e090a110f1305040e1f09060b0d0b01060f020c0109030204022b05040b010b0702030a170417030903011805030d0504060b0d14010e03030709 74
    0x140c1e00c600150095034002d841e030354a103542040d002d1100399100d003003243c900603151007043c00083c0070074403090b1054414500364000c900d0007050050181c41c0c0342104406402a002a02e040c0f4004000342103160900000410a41003421803901040d840c110800088031110707015000140c0100c0214114404039003c180c003011f896040014080809040481c0107180345201c4079000200440c294052104a140442c1200e929598050b911448214100e80b183c805403085408a081c00c081400103141075006042650090100300c858041030701c03207110741c2410211a04040036610401e210038030541c0c81d903160251048420341860101d445e030100766517080600002d0b000742d040d03400d081160011901100c0c020300c4903ca2030400340c0348a05040e80ca035801100c10078031039840d102032803000b50100606a40120f070004051414041e40000c60303005420018011609181d966010314410b03910400751503200b5000321013000902040f00d1100c1d0031244405424400c90340288100000f069004a006040d0f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 157912562 1250 157911312 157911319
    0x3150203100f080a1103011802090a0b0901060504090b0a030809060c0f0f011a030f120c0c1c05060a0603021c030311030f0718140607030e0d0623090c 66
    0x380e03598400408080d0a107500030060b229040700d00000e5440c0300080240c41e2a001d505891221910b4600301030032248900c2c1b125407080709415600c4054038002c0b11403070b4854200080404d01204040010380100f0007600400b010450214051222940c0342c46400d50705401501e60070150b031700b50b8541c01114018451010b00c6004000b4100740181c07c2446141e109000348812104101c6c50140c035030b80a03290700380d24035500c49001c4030617801354940003c4100d0005904006085036044064000f4081d0b404810741060314070441c1d00c401030304c1d120700000d107010400c40c02c42041c075040706103001824031388003a1014407140e00f003010a00242c0e0743c541c000504501c040c031009101d01c8451500364003400d40502d40300c410388800b20402c07499140d08890702e8841d02c2035030303502619941e1900c21640c862241d8002c0c400c0f91900070400d0f2029080ca1801414800d0083c1040d141c6600c0042c00654500c061400488010351030342d030146600b110391040b000d10390140b000003030f6803841c00d289180d56555240754203520 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 157913669 1107 157912562 157912567
    0x31f0e011107110316030c03030e011d010503150604031202060c13050d03050c0102031f1508130611030a140a020403030f11070f06080a0c09031502 65
    0x2101e094400780ca90304001e09912141e0400c1503c440c3d96405119920b01c8140103004445500e0041d81700301688603200303055140c01455941c02e070340c8a0b81030081381d44107a80c104035050038603e1440c40a103000c58a9a66070060080103c05180401e500420000307004814807108070000550310005030212500c41e107448840414920416900882e0110b500d8030903c031914044403a103980038040d2900030b0800003203e241c0d42c00c81c4d0050b50710240401000800301c1548029910040c0100b140002e0b1701c00b0710203e000003400b44440189074500d40c080c88034001c410040b41c3e0740602a00014070044648070b19028502900030801000050365004403030b0002000c0300035074005c80702034960607175421210b804814802e8800300c034001f100210074040c0c4c5001150303101c006646c000083c040c40d90742011909000c85414202c0301039000313030820001c4254003400400c50708005071072100006240140d = true := by decide +kernel

theorem cover : BRFrame.Cov 157733812 157913669 := by
  have h0 := BRFrame.cov_init 157733812
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157733812 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 157733812 ≤ n) (h2 : n < 157913669) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
