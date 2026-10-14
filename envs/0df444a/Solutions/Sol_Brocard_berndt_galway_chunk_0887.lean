-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0887
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:27:59.037038+00:00
-- url     : https://prove2.me/submissions/657bcce4-f55e-412b-a49b-a6bce9849039

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 159352517 ≤ n < 159532374 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 159353767 1250 159352517 159352537
    0x60207050105130b0c03071704030209060d030e1e03070e061f0c020a0b12060904081608090a0801050103021005070312020c0a0209091b0301020906030601030b0117091608031e 77
    0x150341039071075403180d03085d501c4402454000d40000030366008104d1102105421000030008950415081d64003058101c0c5002d0215841502c101d10b000c2c08261060542c01400000640018001600408074444804801c10502d2103402101c00102d046907017070701100d103d994000c1c001e6a841102d01c1520701c2070780800c03030344130100000c903125100980c0313403014504002d10501d5015552040b00c0b0f070310800d44540241910340324201200c1802b0201d0b1092003641c031144425141310000e5462850125058410078400079045104103138000703000c80040d4841030480f40203480f14560792a804204680500c80e00301b00402240881345000c4c421981c90707000c2e00402581004840c81000150001005020100d91070041548a60745040300140d5008a0030300c1c443c2c040d0001d50604840c50009529404018200c0e030402d544c40716155510b0b0b200703680c4100084075002c07450490b0304002285548403e1205800040700142030000645917100204850080580048058030a01c003440c4a42196000389907070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 159355017 1250 159353767 159353797
    0x20910030c0903051504210e010305060105070b0c030109050c0705033405010c1803021807090b0301060203210405061915120c0603090b040609052103071107060207050105 75
    0x1c40015030130080486091035614084e2141d180900d010307040d04029030008041444047d88400c0100d40040040500000c2402c0c0400c880d610540125014050000f01a0041202606000d45d5503000f50085059902c814002d006990f2070907102c0a840c0700e2488000c19070750042159440540300100d1000d800403c280400d4070310411400d4141c0307902c4c51070a098602d40d40d07a20108880070382220804031960240911103900515640004014462510000580000020015040c00d01c62070210014246034610036071a0350f100d0030002d503650000c2d102c3d80d007a040080c840c100280040019544226408802040a075441090842d0f4400c0310016142c440b035110703c08800e00000700d5040d04043c2209070100c400fa15a58180105490103d600c40c00926140c6481c00e80403070340040509910030740048001c0f8001c00640382003490039204006402c41c4a02900655030b40d420aa402540500d201d5034032014280031441006440e100715201d1400581d1102801700815401040030308110360b502200c0e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 159356267 1250 159355017 159355019
    0x6090406150b0c01050610110a03210603080a020c090606160609080c160b030403020c010c1a01030b06040e010e030a030b0a1a0406140307020709020f0c1002031504020910030c09 78
    0x2c0c210070b81000590040c1da035128802c014850420210710305070780400c0e2521502d40103881c0030303c81c0c030703641d07a92005402c100342e8208103c1075031041e04c40000d990407610f17400c00072680e5a0800300d5668000026880050054100d407800c1803400c070540e41d0190000070802c03858004251420a0071006000048503100d840c1c248800c04106ca6030090720490307080714050544025121040c41080d0055001945010000e10501000c00d9000844c0006d021080c28041c081c15418200140180008000300303003d489221b0003c0200000a481c2c140108020b40b0140140b4403840341c030600380caa01c05240c2c0c4c4140e03c1400101c4400b4401d8005070384a8801070908060701da29002915208101c1d400c081e0750b017800001e420411a42c0c401c00805002c100300141900f5030400400c0207480d20304912808081e035030041041c80c400c4130a242100c1c1e130038104400311920112890040d80194004031a165601c070300031a2103180301d0a00380210780d140c040c010070340035201400030b80035001080fa1700310314400c014003500 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 159357517 1250 159356267 159356279
    0xa0e09010f050f0105030f0105040f0f0510110a030506010c0b0f07030e06043e060307051207020a060e030403030203032205190b0105101b15060f031205030609040615 73
    0x114143c041c11100020a0b900c2d030610701418505454010105c1c0283c2c902800c00c400301d8850902e0418490b070000e04d400c1d0f820002d0800c40d2030480350700e6003c0381861900030300c42440c00c903110080800c61b1650f2400d01032952104c00640d2a401c801d40054003449040d000100c05001c10b803191540014641400140400700e003481324640307001180c003203441d10000d0344100100ca095558445030302460035051080b8100300883c4101003a080c000e224021680400800c00550158054031418000301c0c2c071040040c0341101c0002e503100c0318118180c40842c43c020070031000039400f00071502a02d4244e00114074580300d400356450b9034401043c0154000c1035040f4030000190040c05074902d401103109141860910b1401d141c2a00501a885203100780e0f5510b10880001d0f400c0301c940000b050030010404662501ca050050080001032381050055280680c081411440080c20105a900a64100e658440d541a0030780d114401510020307804000200001d00054a90f08015402c55452040640103a5504 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 159358767 1250 159357517 159357521
    0x12050d0809030c070906050312130e0601050d09060504031103030c09010c0c151d03010b100309060b0901151101063005010c0507021905010509010f0c0b09070e0c090a0e09010f 77
    0x6000003000c06c4e01c58030b04000318a420091411150341650344070385041000d85000d41481c042c1d100c5c1510001480d0006219a80540c050710190801807034107000c1c400c0c035850690010300044400b2004504000f0702c00030001c20002c2038a100390300c0c100e02c0c5442d00110b040151902d0003252070450700f444005401103034a00b01000a0960b2034000d894100409080080440040c1c120000c1180030b03030324010500c5032523500ca803540f511240c00e40c14002454800e6040c110060291004c42580180040000240d9a031041c142036000e1402552281803e40c01e00c1846400da61651040f1020452004001c070b290705c00305114180d041003095040c0d100d020855a075507007502c180032800000308001250341402e40c1802042c0080c0c0d9104500c0520009003000d002a103980510342c00316040103900c004030341d0094040c03010340070008d403c900750b80310a00e040108941d030b80c4010b01501d000e0000311000700b40b0a4030340c201500c210349002400200f4880c10107010180e1840000e0400b1020364883c54241d182c01740f24 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 159360017 1250 159358767 159358769
    0x103210e04110d1b02100c0c060f0219080916030c0608060604090c0e0f010e090c0306030a15090606050904030207050d03120f0605040605011407060906060b0a03060302030712050d0809030c07 84
    0x9505403900742101c0d51000c0c2c1414503000c3c141a540c0d08008a148005231b20007100030510381c5c80000020340c0801180800000d004403240d2100004440e402a5041500075445a10600929007202c06070741c0b040001000a843c1403000800cc947d50080c00c2c4100c40c01041034581c4514050042070400b690b40e0084030940e459141c404020403402004060241004141c89074003501c2802c00f9030b0131450400100300704560081510456090200100f1942d59003440b0101002d900700d01c0d84001c480e0721000314001021401011a2420700c0c084001940e810310066840c0309640540117880c001c3d00d801c0902401d088456002c508224408408036041c601070703c200d0719904901c240024440703050005100031a10141c01250500150341d0411034450400011a001c030f5070702c41c50100391807c07185041d6003d4407491700240e80041e400b00d1030030a11603141d442038084900880441d01096a80c8200c0301e1500740e95a005021500900d1210000174007582c103c2d50007000e030000301c07450301111241545c100405 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 159361267 1250 159360017 159360041
    0x3100e0a150e06010e040b0f06040b060c03030604060f060c12031b08090f032b020f0a0809070b03250e060a120633020703080f030103210e04110d 64
    0x340310b00107501d002003000014058005545041c6070740c10207031611282da00c0c3c01000c1c544421000d40000d10240c5860b00a1183c996014180d183c43d202070001d40b0752070303420488040307004a2414400203400b84100c240300040fa01e40d500c030300460502c544c07980e2945040004c003000038951550805010407000d1050109101c40503501c0781c2440c2800d060050900040b0301001c406039005100c801c40d03072010066066140009100c00108844003a000300c00a805140c0c1c8203909030700c010805a0980341c11a103203902c541c00e0b1714107440c10303039032103204c001d00c1d902080e5101c0c1c06e0200d000c440714040da00c04502083c42c03002141042421080d6603c00038a40d0382c005007040000820032050b65024003c1400741c000a003400c0395000260100d20080b403c052000804071100c11200c91a1204503c2e00a00203480a50342200d0f80990702c9e07000b0600d03842503078004e1000300c1e00c0160036010880002c2e00d51559820f042010741d520013080180744100009840404003a4403030100c10000400031451900c6106840341d1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 159362517 1250 159361267 159361271
    0x30a02040e1509060901140f120706020d121806090813061206050103110316110f01020703081303080105150918040303050106020f250306020a08060306011403100e0a15 74
    0x24450b00784010800081c1140c1d0041c40302100504c071007200040c4495503140c0540d050305010160400007180d43c407003010035600500a175140450001d60200300302c141c00c1030702e44540200344900500d01040350300c094151110b02c154404040300045542c0c0040030224041c0400d2070030200c08400101c0741090561000c0c1c003090700407001504c8900740380074040080000742000c01041c0c582d0204000c440c80001c4c03100d41044101d18401d0b417030702d010b00d4802c11454003980032030300050503079002207000b503000714403c0d4042002000000c611020090746081030701d51594948075981d2070003061082c081100c12240007200024028003003503441c0d420092060a880c200d003901c01b814103082c081e040711811b0308020215048590095080d54000170f50b501c81c0442040501030604d80c003007d001c0b0714417468000600440c00010b481ea0380a90141b195400f0f101c2c2207065400603603031101030104010100c20840e0309070b0800b045c00d09d144101507000d0903032100e0500944083c1c111590b60840c04d8000c0c0503201c2d900325 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 159363767 1250 159362517 159362551
    0x10c020423010909020306041103070317030f010b0f070f08090d06020405180f0c070302010b0a031b09020c0a0305090a050a24020303070503010306090507090203150f0f15030a02040e 80
    0x1c1030081c0c0340740100820a010000c40c0c0d80364010a48440d00100094003844000d4103100c1a070700e041040300019604076680c0201481c01c160420400d03402542c00c3c2c1d81d800444c40010030410f0417070080341da210815909143c54120300355615250507080c0d0b13505450001040c889010395444010000034241d106000043e52642010100802e40d66200003155500404000300300c400368100090765042200c403105140c4a00c101d00c0e04a000d04a0100c0603600440d07074090010030000c8840905101c441401c4603903030381e50344070000c440072400390402651195205103190400700f40100700a015000300540900496500c80f004a0380e110301d681e00c15030146007900e0400074455000b86440d02c7d40320241c405540386044c0300000504602041c000501000e0340c0d4040c0c0020020304225000007003904400a5480e4641a04021442c1c2c2120350002d000d0400f8460490b804c1c6031801440111840051224a141c10540900c00301500001e1000300995401c000100310120180d000620850070048503540300 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 159365017 1250 159363767 159363821
    0x10602030408150402030c21071202030607080906010b0a1b0c061701060507111c050105090f0705060d021c090809010e09060901050420030906061203030103050c04050402010c0204 79
    0x105a00740c420103c606501018000140c0d00400c2c0030103c040100c80b498203d1030364086003040c0700d851400c00ca050740714503d0300040d0362030300c040d00d40c4c0482d00882c2a01c040350b0f1200070985440000301c40c1038401d5000b100044c01a91107940141c0109001e52401040308501031001c01c4000000001c02e0360f02c10313680602041010740c000041d0701401c99012020301749514050019100c0c2c007550100404050600901e1089610780d1600c40078182e0025052804114407030800a000b0035003907400302411700948501a010301c0000916108030303803000d45214500715010000c2e800a40001c4800305182c00200300c4411460441d0203420034660140391410780d0f41c04014005040124415216030003004000308000c210ba4131248802d044420686010400c001d0140d031152203c040d03001021301e0f0020100034800580350000e10703c0d104034002d6680002c07c0d07580d84449503480c042444010007940c4040319005484c10300d500100d40162042c10700d1003c40e45903900080640b0305c24a4180c0c40b6001542441141e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 159366267 1250 159365017 159365023
    0x204060e040b011a0901030209041e2a080f09011e02030708060d03050a11031c050901050601110303040f020f040507020c04150b2b0504080c0105060406060801060e0a0e010602030408 80
    0x10411440e602041504d206070718642070061201c094181640030450300301d181c07140c2c0c000f40c0d0076060941140003011403480d02030004001c0c81500030350382c61558494142403100e80c803451100c865030b52a480750541d0b0b440b13079981c2e04c450010302c0b0542a540b00e0160000310b010030f0500d440741c0d090384a070150302c1c1c2ca0304400c014100d110051280e4400c0d098078800c000800d8001c0122982141d007480d01095001c07924590500d0341c03180c0b000110b1148031214040c072034601a5071202d40140b0100d0003c1c08561628401110f124041c1000d240c04c0740c0042000c20000b44404240c0d0180301e1018100308038000e5030b81c000508441f4100c1eaa00003580100e8040c41c0036240521803500034100300014003a149061000c1c211590048000c0c1d0449200c51000c62800c031000c150f1100b00c0807003d0181400146000e180040c0a80c00c4504900350039800e1102103803141c0703041e02911081d6000c1d699115180c0c4c1c80d0510444941c2944414103421070150013020800411202403140030304002d400550307a4515048040345 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 159367517 1250 159366267 159366269
    0x90c030604020105070f0c0f0b040e060306010501081f050907080f1605180105091003060303020714090406020906090901090e070503030f0a0c0203030c060108010c08012102011206030204060e040b01 87
    0x442900080d04101c0181e810409a44100f50002800340d5030000e540742072040038115030000295203c03410700c00108001030b40700070400d603142d05000c07615a803a101e0500d80d90b0305082c002d081c041000303000080d08110382c80d500000100c00c0420410001c9503154046507500d982640c220001500e42001c1080440e1a074440713540020000070295006c0a001400070007501980c008010001c90b800740c03a5034960b1040e4103a800c0610000d01031164144407540c0500101b15620080340035018010300029001c0d9821451800344101602114082d60b075951744200951000701040d0f0f20000600c960201034803140c0d001c90103000c41940020b805d04000c40130070301e0941154441c6110341d00801c4407690a80c61602503901c54011418240040e0343c80d440020300b14001d440742481d4a2050800000351820150003410100c0b0854481d00c41c241d8130381d60b40c01d07124034522400c0b103074000f090146200154810b007110742c501c000d00140010400c0e00ca60000702920444c0d40540c1d0b078410204140414040041e1a0b14 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 159368767 1250 159367517 159367519
    0x12030403030614030a02030a060c0207030803011706011e0e0601030204090515150a05040905042112060f0e16140f03041205070c1a07121214060a0e0405010902030d08090c 75
    0x3040170710666001a070340d4140180000c0c000d43e107404040200e13074020001d50016580c03001510b5140d60310b580080188c001c00d00c0704d10290741700d002e00001740b01012204034205804400d000c0d010540c1048841c545600c0c0107402ca03030415908010014040d8402e114190048101240c90030702d51242d1410002881d46044005400300c40401407252801d0b0000203ca0031612104d002161a54490a000b03108a4030b12095103172a4520600c0601101d600101c10314441c034140c0000c101c0345403500940d01e92254075009145418100501007945e000428a03841407102d2580307440c445e00048d83c06a0021504a1016030704500e6000c0240010082c0e0074250611545081c80c00c2810600030303480307007a80305070070348181111100c44190300188209080c0c2229400f40e01f192061307a403a41e424800405134199428100000c0349421150300c012041d000e81c82d0300510004007501c1c0300303c2c100300b0714107012500035000b11559036071881c9100040c1c03400c5c04040e1745220310b929803c07203d01e0044c0c011801c000c1013061003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 159370017 1250 159368767 159368773
    0x50a060c05090d020906040b09040b0103060608032a0c060c0c040501140918010b030d08011d010b03180106091103180106060c080703020f010509030306030f0327031203040303061403 80
    0x5402d050b10340eaa600d501150b0120b440b0785494035140045001005422409500300e552241080b05210078102014101c0e03124503c10007016644803801f46d200d019140114807460341000c0e1044c241d28a1820741d0522918000507200f4070b1001d040020640e502c2010f0300503481e004290889842e203003d102e001d00500201007807500340900480083c22403000182410780c4104001c80c07042c1c0241003544035500e4000d0240454004810b0078401a1100800344110a044190759174610642803401c0c2c013181c100e5108040d0a41140c07900318031450140c502c00d402444035940e07210009040041401261440003000500c10f642e803d000800b421003500211840d01c07240c1c1424801c002c40d54ac02190300001980080e02c2c580c80d01582c0c64101e061030321460842109600348400c5c80300800020005602900048040700c0808076006400c942300d015204906124000048201c0c10202c030030170a448900400406a030011804003002440d290016078041d80040c0e620503003801070b104a01100a1f046c4d4007103000f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 159371267 1250 159370017 159370027
    0x70e0d20030f100c17131103030a080403030c110115050901120b0703020d0f140a0f090228152102030610140904020706020c06010905070c082104050a060c05 69
    0x9036980c0c90354440e01c41a10140d4413850f55a0017440b6003e4030102180d107850891650400303803810043c1c03810314081030318020320382c00403c180341c50000211104140c0f10345580486654646090f802007000c8a0441c050018aa180010946d001e1060148500302c828000d541e003402d05c400d104800405820800c00c0b00b164040e0308010442c0080c050f42d0214403840e01582c1c8642c0048244050321900a0314a00581000c0200104003803008003d44903100c0c8803401c01011000800303c0c815141c14031030103500f041c0711288000e8103080a031a04400f11030b00c0c0d10340d55403d6540e442c04481050f031180000300040c20b1180b48038403000d00d102c1c10b0719440e440c0070400e50443c28980d001581035030b4418110310070300100b84020528810071505807803d110000340210b40394121402c0c0240030350b00c02c032640785d52405000d0011078210814842d181c00b03180141d0343c101152040d07070345411195001c608807001c02041c101d42d950085002104d514030551040c000703002030b011a40f4040c002da419a0103c032003440000c0c00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 159372517 1250 159371267 159371293
    0x615010207031103010b0a0b03060f04061206022505240f130212010608030405190e0f0a060302040c0906021c0f051303021e090c03010e0a0203070e0d2003 68
    0x482900b500e0704401542c0500c10301e400041e00404002010700c3e00700d42c0c0000b000a00c2030700100514420131058450f000c41004107401c000c1115124040e6210032800b400da403a01084136070f0301401010b40c914100ac44040304900107000c440c03504030000c80b5140d000303000075070300f030300001380c0c0c105200c85040701d51a0705e820030700502d152200c402040c0c000642d4002031303901d0941d550b42c50b401c981c2440140081019945481940d9103a901c60f0180d80d00071500b24030101c41c40700148a4140450b201d414048216440d2a04200c06052014000180c12a2201c10210240ea2103110701809035070907807a48540c0901d8080068140651400810407030243c040008041c941c011161807040c4000d850426520002c0c0d02814144000641020350001c00c1c580d0600c0d10900c080006024083c01210009243d5442124105d41440b09008152420751401c011903003000c540c0e00a181c000c0c0b820b003030240c0f44000c031402154a030b06e0038410603100d8038804070214451600807460400e622800754080d20850352002 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 159373767 1250 159372517 159372523
    0xa06050903070e041a0a0b030f0a020f01050a050c070b0406080a1808030a060e10081207030c0206030414190b01080706050f0a18081b0d0f02090702030d0f02040806150102 75
    0x22080c80d003581c0f1108001400c210f215034014520b0b90880c181c0d8485030408049420091100862043c040d1040340b9a00406403000603104201c26402081d4a03020ba4607400110342c85e030401d082080a001c801d22010351003000c10b205d094040e0100c1c50086445914150004150f400c004c0c00c810001c500c1c1c0b4803114a41e03403c550100701c0c0306401c0126503a42e0b850381070f0980000d181d9580b001c4c058400e5001409a00b50600c45088212052801100d54a01444548d10388600c074103070008000c00d42000c1c44000504001014540c020700030361144031451048034202e030901c140d140f038442c403495040f403c2008005482081c0ca0245c412800140255802e120000d0711500c2070380c080251869010403903500851081c0800030041d50060864040240e031600c401c1d03503658058403010302c0c070000c030b05071180c0500302140c00041c103e40042011220150307075000d002600802900150440c0030401c000d52900c3d03850700440c00800c0300c401c80183d4603413900c0102e43c02d01e00060302058107030020401140349682c0c00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 159375017 1250 159373767 159373769
    0x210e0601120b310c03050706090810200403260f0d0207020607060603080a030c05030c0702040e010b36010302090711010605150a031505060406110114090c0a0605090307 74
    0x14640f0f0400e180208102c400c8107110768030044448084441d0b040402c141480300b103080742e208404455a0944030f0009450801c4240600d070141d91156800b60301e00e041f00d0700011850400e107d403801800c480c00c400c2040c1584550016030b4031450003580d640c090300b600b405811428082081880c10030440c5044450984500700300f088060b5004183e003c00d42d0b030f488003101d01e800d071b00010400c0000d64910740b03100039801c141e0003040031a2628450050380c0d80150f0880c1c0c441c0b03040819091a108107a404c20000703004440340035051359a070b0000a0003540b41d80c030900c8a4002881c1c2c40480b5903d140104120303140940340d04070b86042c8148010070050311002410783c0c0044450405401d6684200e402c207004002941c01268800502d016005c444d6207120001d205901955405201c801c003075544420030900c0c81d1041c035130420703001c2000300704c0c4512071054035008480841c0082030008000000c220008000d881c3e0313402c2e64000c107034440c0d00751030b0075158500240854100380d4100800940003980742d282c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 159376267 1250 159375017 159375031
    0xb0301090911100305091209010e01121b02071a090a0b03060d0f08090901080a0209010302090c04120809090106080712090201050f0304260412080901210e0601120b 72
    0x558a040d8208509550b041103010350140803920400d541250050150505a4502049003e07a68442d402803c000c006c0700c903a0401a100c05010490100c0116000c040c0328510b41920b66848048503220080051000f118101541c000e142072070600c0c0300d2461000740501c0b15808400c081060301040d464040121044a0350219215103aa0340c42002c1070807982031140080280302c04c00036010030406d4a5024001200090300c21140e50f82c4c80d00c213902d0b503038420444041d500c028000010001460020510303603000132a00032141c201555558042c00c6021003c000f20307000c4902007504c040d40c9c00c240442c503005010034603045c5603a0030001c3c009031034610315010010905444000341800d5900590444d8904800d2404960703a0f0b00c0c140c1014070742131524091103040421100c00298850191500382e400784c9100171600715170100c996a69101c103600c500070f0141844541d2175000c1481103508101d464860780b0100c040340d40c0031000d1506050600c16048004038807810f00c0b443d4042004d04600d00c0d84581 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 159377517 1250 159376267 159376271
    0x50c120309031c0f05010e0112120509120f1015030311151305060a0b010f111c021507050a09050121020c0102070501050903030606070f0c051806190b030109 69
    0xc80c00364242c1148258829006801c1e200c0300440100415607001a0328141480010426641c03500809401c460080c451485034030030382d06038400443c2c1c1e0284a4000c200c420304005c0c0c80c2600c1c40002c103002004414007401e4540004141c1741e40030809001c40c482c46400d40034100140030302440e540c0903c035018000038081006142003141505010000c1c2501c0421503100078000e0703d4081c9040440c4011410101d07014000d24001c94040c84030b900070000001016110388041c0a00900125007468150352001c46502c10034554050a0a050f21882d150f2480c0f0303405007030f0020820880800400c0054040403c00c03101b04543c00820f40c0c489a50010782e082440c0081c240380511902c261800340280245a42e07520018662086050540c002c0454522540080c00142e68001d07056440340003c9a485400400822242d80050841d075405000907206080d0620400e850307170003184403856050301100d06e8910550900105240c4151680c0c0e22034450b405880049040403403280715400103210329003ca039 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 159378767 1250 159377517 159377521
    0x921010609110306030f010c120b0628020708070308090103092f010909050c12040203030408030705100b06070c06030e0a1707060b06160f140f07060906050c1203 71
    0x110290000c5004101007070051103516450321000e6007540c010748140b03100c0e1044003480355141006000b118400c001580792206907100c250161030140c1007206225a00c07000802017900c1c0e48070040343c00080940e12180c038580910408801078544101034020108551100c0000c00016558404843d401c1000f031901003061952482c00d00b280c070f0041c07100c2a40c2e1944416200e010b641800b805401c0100017642c50010803695071284000b181c90640d80e0f0440c0d10303000c2146a0050548580070342e00710384098112807070b082c0d5a91040d4103540160744101c0fa290400c3e04a0407a402e941d001c0c840743c0000440d801c1d407401a00b95501c400c40141841074206040c0c9400c00c070303182860f042c0554016039800c0800304503040103010200a41b40d0282c0c02c1280c4440c0b414140040388c3c00c000007504c241405090314605140425100c40d964030400003001c66507901c00d10b200c1c5038040da080c80b0b0a807007280d0300001080f1060800342d01401c20805a0001001c101040c130401c0203030f400000e01a1601d8401200301961307a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 159380017 1250 159378767 159378829
    0x18070c020a0918060c031505120705150301080c120a030c110a030b10060306120803100f08031c0b0109050d050c04060305030c06010b07020a050906010306051201020a08090309 77
    0x15101640840d03401450f26503c0b1140030f12100410456a01ca060204050041200c0039000c0747d45420710b03241d01450f4460240035500b00300072504080c880340300407101510380c1c8900003a0580461033300303d100d048011004001c1f05604001200c0001c0c400c0b9810380513007405c24182e40d500c0e0303015540a810440d00c0564403043c00b0b80e41840c5c03004e84030054100582c050700da00f022070708400190f80b80c1c41c102c40d13290000503190340320744a540c00307907065000c901000d0360003519503090326000941503e000001240c0c00007440440c000c00c0500401d402d030701540d161300042d41031059401000043c0f1f901c03036041c80300610340c50b85e0141019042d22001c442c070680c20340755420101d00d480300c2002c0141c3c020385010030200a014000020f07041c552035040c100c4105070388031700c490a044c0c0280707003009400c01c0442c4001e224074a00f4500c07003507001806140c00540707659540c0005204100d040b05404080c0d40c005100b20b0201d9000e070450798024508801107150200c01e00229800180d11180040c00e4240c044014180c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 159381267 1250 159380017 159380029
    0x80a030e0934020c0406080a02061b030d0b10090f1a04030b0a0e1c0804110f03070e071704020d08030403050d050708010501090509091b150d061418070c02 68
    0x94540684000140c9666040104141080c0442c0c810090300c0b4512000303469217000d004050a8030001409003a07015519400d00c1004d400040b50307420700e000f09006481208030100054070000ca039651010a0308100035061003a072041c20b00108e810000c141c4010300001490000803400c8504401540710040201501b0000c24062500010703c10348050080c440300442980050401c000340009940360841c45400b03003005e40d50342c412240e01240c004d034001004590140d0a02c51804c03c0a06408140c03c445400682001010340045001d02c07410390500031100d030f003c03580f50301d074910b0302c045a01d060400d6000508c2144600c00000c2c001e02c000000501094425025031f03e81a040110900442c00e14500140010b9800d009090001c1c0bc6080006441d20f04441c03224000d00c086000f5204052048510001610a002055401c141e411000c01160900701c001004002201503000402c181080300200c2c0f01174441c42c1d010b00c18410b1070380c1d2800c14040941c070560080d1a50a080810702214400300e11 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 159382517 1250 159381267 159381301
    0x3300e0a03241401030f0b150d140c060f070602070602040b07050703020f27041704030318080a0203060c0304030c0209011401080709150c021311070c080a030e09 71
    0x82401c0041c4010b40c040c6480074030406000d856006000762400790200602040091101820b0b04800c00009000f16007008070503034018074000c440c501c007407007181c000c2810f000804404444241401071920100d010921141c510f040045600c00e140c48040d12410b80780b40100c500c040c054030340c0000c0300010415240c2c1110010150200001c0d04c4412500b040ea480f842c85200c181d0042503400e450500915184030100184414005520202501c031100190740f61030003081103c0c1c4003032900710700007003a40711009003006520030381d61a1100244801010780c518103039446a04150712200c54180141d5020600c164012000b8003065100d5446003070032183d072200034901a4210711260004110342003040c5060100303040030b88840d400f03a01c403a4011254807104e880f40c0325450007080c3c40744805500ca510021a100e0004060342d01203106215202c00300d4100c00c0e24860440313000590b00c3d041201003202000200908400f40401c2111a18058607034400008168458940c0705d00042856080c000710758 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 159383767 1250 159382517 159382523
    0x61e09072d08070e01080d0c1104090530030705040b030726040203010b0f030303240a090905060a090506010e13050d02072d03110a091503300e0a03 65
    0x140d602e541d000403949914041c0186a0000070072400401c6040700012440035040c000d41c2d4a8181c0d0200340c40b12101701350407540e860b901c5034545812001040c0b08100200c03120a914442e84403001c2c2c120280710441c0c420344080d044203c02442000101e9820900f40e030200c406c2d015502d5a65550103000320380300580300403d0100601202e00140c181200203114500c91031090b0000c20415007074108100300b4600440d903259155200300000340601d0324003404d68880c41c0c051680c10300940d80302d20000741071142e9a040800031503521001c4405002041001c030703030440c640c1c07201080040e8030ba071607040c3c480070b05000c1c1e83d040c03e80c010081040c58030002040c2c130070746404ca03041d591103802440b8020340351000351160600c1d44600d692200000b106401503805108221030031946003034a1a9101c40d07888001d81d084a46c40b0400703020010340c6d07e5407802010310410b5100c244100060540c030f0718800c005801c03808095092010344c02580ca0724144610841464040d0034011120062000010042d0403a50401 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 159385017 1250 159383767 159383849
    0x8120c071d0a060e091f06090504050f15130f030908030c0f0c010203090a180905030c0d140a020c0904061b08060406060c05030d05040c09060305061e0907 68
    0x2500d4451241c103103403801420886070074040142d8400a0000042c0300f40e4159405030007038000386d03c4242c0d01500c030030f0601c1100301d4041400c59840035800200c1c0c40440307064070a070b00804070721100f184040c0101440c0d005603610070b0030030b810000c40149180600360002001c058291365082c080c5801550880e0080900710101c0740d40b144001000d036202c1c501c0c882d0300529446100c0e6068820360020081d1800c0c5d00f00502a50110b5142c159485061095070364032071038041d69855144080f4405100030032000c0c03170b035000070a541400718600070030044050a0000002c0030602000d4204d0b5400b08201801d503400321007544154446007001001011064078883c14440354000001d220f40d0171001051164004950401841e940c1d001c0941e050f68809000400c01e420412100d0681000c2ea803010f03401c0fa006250340601e172502d422440045400c2c0f0b400c140c5040d840035040010044180d61082015004a141c84500f0f0800302040c9699041601940070003800e5401030700103200500b40031000409010400c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 159386267 1250 159385017 159385049
    0x60309010b0a050906060d0b0d0c0602070f0b0f0301050d0212030c0a0309080105072a0803240a050f0d030c06060605070309060305060306040807020103020d05040c1e08120c07 77
    0x25080c000d118140301540961031002c0c0010b160724048034500d1040f80050038003850441c45080d060020300c1c0d8101c0030748d4407441c18443c010100e05801c0c4840301130002c58004141c0c550600071409189451176010101d400e1041141080c400c03507000c1968115071080d07407050031550f010f10000f400703e00f4400c9001c0d988e2202280c0380c0d0036040009482d1a120b03010f511008543e81d11050007600380c2c1c404407105004540c6030b4002e0903490504a0306e041031302c8580310407256050b2190341e90007803075030055603d1210b5400c41c592008003844802d40ea030b8440c80044411a000e18509804203485512104442c0d03c6000300303041100607d4041c0440180c80759001008115298980310302409a40015106800141048a0200c2c211307000e885100d01030a8001c0040040d50340c0e5554441d042e0340168030403410075400303000b00340000d1114000e00e40180c1c408c24419080d2810020320070404a0712a0000c034050f859148108020013010138520108483e59040c156140900d1900900c1c01e0790907440000080c881e00d007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 159387517 1250 159386267 159386281
    0x907170c04140a0b010512070813120801091a090c09010e060706021207020a0506130f1406090d09230d080f0702030d030c1e1107031a01091808030403020106050603 72
    0x10340144260f07079001040200310906001100e00e80107001c0b8004e0008403a1000c1031700180500d410642c0b003500548441d500740321565600252100201000001c140300c0b0006001e0b0031558080c0c0d030740148200100c600105048000510328400141081d4841c20000400078900e034440c0c04807800488000c1d011036501d042918050009502c00014812001048008110b0007403000c60800c10a942140003003035a83c40b1780040065400c00000215080958104180002001240d410b18100b400c1c4001d02520301c1c00c000502c0c00c01500c51b00c000c081100c0400213100882c88044000383c040100101c03060b03051154000305031500f0750584094241d6801240740c2201d0605000200f0030540300350141e03202d0702c445107030540c1510390304840280856050020002c1e06d0400005002050000d0716002860382c40b40d500281c140301c03103038109651502c0c2c0091034034948050b091000d401851940ca040010041010440034807034244c84006014480c000003207418135100350480c401138140103000e5507481c14226 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 159388767 1250 159387517 159387551
    0x11b020a060f0b031b0f040e0d030e01020706060915050105040b0d0e031e04031b0e04020105090103060e07110105100503070303050a0207030c06080610020606061c091205030910050907170c04 84
    0x1c11070920032a41c00d580c1b420f031810300307000711030200b61180002c080c6108100e60980c040c00e07c881c5000c0c0e280d90700303010040c04501d25010f080c0041070109800140038111500242d2030004981245044c40340030801003005440903070441d9801d0300802c030001105031800c40c0d50780c214465031818000d002c2e440003003981070100d140010411240305001684d9402c0384090f803c83d0520316032050b2004401078100040155001308000c1600a0301494009000d40d110f010600d00d202c4155020000a01041d02c1074558480920406801002c1071003c80c9075a13280c400040d0ba1007880b400000c04008011450041040c001c00c004805140c3c4010401c819544680f00184000c2c01140d071184500215a041c0440310300104105024010280c0410701d401e804ca54009180141c50010170103056403a0a07243c085003060703045140041c043d558456507414680301c01c514003c04024540f050516050600180b0000019040c00704da00019a1514448013202d909050002101000781c2090800b02c620301d003001c00c5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 159390017 1250 159388767 159388813
    0x3050417030f0d02040609080129040b0d08091c020901170708121e071a060d0b01090b090105010807050d050c0f03070f090f031a040501090512040305011b020a060f0b03 74
    0x247c1d81c0d1004e06956010b2007800e0b02c07400c0e40d0403500d460501202480700c1e0721028541900c40c030041c001203080d42240c4003040017040c2c0700350191416480030a102895192103c00c10b8942c0855000c041c0c40c0340f8603a00080d0f40c071031040c4203005014040b082d180c030031010144000d400038001d54041c0c030040e00140b180b0030810340c00041000048400c4003603c04401451034243d81d0490342004c4401d00d000281d000180010320f0240c040d0740d00501909a240015030324030560b6001e025040381c04590410144248418880c060300118144114a400c11041a034003c0644041b103c07110f030082a261a00707200c5949910030000b141070003400000c10050301d1900880d8201c0c014065170703a1440c8481d51140507142000007404005d000c2c0d1040c00703408140103440b100e000d80203402040001411031003540d4480c42d040300d54211280e84500071404100f800700070303c103a00800c9625483e241010401000094482074000340081c40e05035140e40718120100f85501000300d05201400b1152010400000b0703420080ca0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 159391267 1250 159390017 159390029
    0x6031606090e0105100e130b030321130201020a1104020d1d0f03090109091e02120f06060a080f092d0111040312230412050c030a03050417030f0d0204 66
    0xc400009468140102101e401105e030755a4081100c02e0381c02002521203040758100041501c0e144440001c0d58280000c03d8081035154041c40448026001824100001403019680e44580c44190000d40d8001c100c00314507076449188801c0c44080200010002e0203003000f030010345032510b035242500c032280e42418001d440c0c0c00c504568821404825285c0e0340c0c070804421600095190a04001d203042c81d400051660342ea03100d80302c00e10580705941204a800031001e05d03005d01c0b907800c140001141002c9032250001c100356030891030400c1e80c80020300402005442c000360000514006000c0700f10a00000000f0003542d48056075401c82d140c80d49000e1301d60041c00c070809506e00302628483d4a036003c1100c0460b0b0b070140f40c000012a004805903105074014030264a01d4041c200140042d000c50710080016007c600c1c00031400600504046203041121141a4000d50140104c0404242c1160a49049030035075065182581a011420742c150b00908122086030000401c6032081c2e14001d03000b510680b01 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 159392517 1250 159391267 159391289
    0xe15180303070f08061e010c050708030309010903170c0f0706091523090c10090b0a02070609050402070221070504150503240f0a020f0a0f0201050a02210603160609 72
    0x5c0708010040c00d40700c0000030641e0200c1d60140c06101d540102100710101d80907400f65217215944d20052415a84200c58545c51a59240d1941c010940c1120f2880c00440d00074003080f2151424070031074040c4d4442d510840154040c00b055000070842c10750400a140342d4031500132002e4540d441034640180015a412121040c10300a1b210741d828900d0348070511444842006280d140d0020051109007001541c1a104000c00300e0408201d08000200520a4940a82c001c00d0030313038544040244030321220f4204920030780c010000200541d5a0f5080010826503494082c005a808160382c549000c01c0399022940150030000c1100901c0c42150742c04007210800e034245d0300403003c100c20310300351303540d0b07030112454610750201c08250303034101e100500341c3c0c44074401c4801403030300b007001c01d03e501c460b0441c180710400180a10002c0c4081d0b542805502c2d0002c1c0140000c0d0b003449012104180f003001420106098449070b00006011303940d0410419110a508034410b0a0301d68070380348001c03e000c0250049050841c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 159393767 1250 159392517 159392521
    0x2060103060f0218040c18060203090102100e0a060c030209031b040501060306050d080702030a0b01091d12250609081902060c0904150306020a020705040e010e15180303070f08 77
    0x502c4500840d810a400d00c0700005074508060200310040c008007680d40100814001c0002c0c0740141c50b06603030081e04140e0025a2100d031510002807905a280d62101c070500d0620003005002d510004100f00000da000b00c001c940840d00030310480c000d008041c2c6140c0c2c10320501114401c0c079140200040030443c016a0140510781e01c0310710907010b4900318030807a03800110907140800459039000203000e00901c0241070705d0490300307640c44910b031024080c2c00c031301038495642c00e1a42062002c01850400d602d0040080c01c0c054030401c031506814000d4280380c0842c41e20940343c00b0b5810440040b001100b40e4882401c00001c015420880c49035004198005010704440301c0004030280002029480b80c1105c0c400145401004020301002d400b0078003412040c03082440000c00043e400c4d00240c104401668018140a445c0900f0071080e40c889202c2207079a40d05d841603045a01001003011505402800407100aa0b05c902c014070140c05468001c0b0401404003005004410350300c84025240040c00c1d5503848016 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 159395017 1250 159393767 159393791
    0x120e100902040b1e06160206040e0703050f010321090509040c0e0709050a15021f020a260106030525020601060905061801080c2505150405060604050c190206010306 72
    0x540140000d030a840c13102403507110306864950010148003000350340740002048180c0c08950a80c00541099103d81074007000c000348680d041c0b00d5980d1100703c0d1180345e1215459515014115100701400c07240810840b80d8401c0c0d103e004d041c0d403000401003c1e158118510740340c103000460b0f0740c2d180103039219041d1800108600c0e030704c99403521003900d000074820066103182020103404181a60030a0095008038160046580600c04240e854160885400759907144001002400c200c10705c0841040e521914101e03c0a50441410542c107460300d80c24006642c3d22400c00e000020221202d105800d81300315180112015404140c9904880c4280c9070200010349a4041048034060f004003824001403401c802c00b020b43c85020a181c00c042a00810b0f898000d071440c1959040e0300400951440d0b1008010000c10840b00304090850b822941004031030900341030751280e4407480041c10581c0320380c2d2034a000c2039101010340308075059100d6024201007048004180a0b454840134131098031000c0ca0b000c990544 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 159396267 1250 159395017 159395029
    0x9100504060203041509050d0b0103120906020a02060c19080403110d080711010302040518010806011d0403031104090c1e021609091406090708120a080403120e100902040b 75
    0x241c0780590055810305080c10a00485e0b2001c4500d07040400c0409800001e8503111f03980040a0940140504445581107040c000513080c2a02452404c004c4e810700100729003503000c17544110407a07046404503500c0b800b0002907480c0551081d014110280344c1c003216400c00445200a1045a129004440c05043c105003040119950140702525520040084d00c0000c6c901507440102044141401801c00e61505c010075640d581c5a41c59024546100005111500d4104642401000d200e1150f1100030042440d50715681809000101071540300c00148008030311035410b4401802c20180200300410010f04024003021414104845100e0780003078070703440c591011404a00c03600401c00380c108042c0c600700305000105100d5006599184040100f44080b02c002c3c040c8034040d20741c40340100402801c0400c003a0802034113059440c4d081d14104081d0541c582c000c5409035000b03406081c00e81840c41c1e80110000035000300c9018004500030040714449a403101e078081c1c21014002d450030400a0441d80038004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 159397517 1250 159396267 159396269
    0x3051302060f0d060b0c030a02010e0a030507021201060317041d010303140d02070804270e07030b0c07140f16030803010e0916081018030e0402031e040809100504 71
    0x900404100320042c00403010000400640300b00943c00940180e550302c04d882c441d008480300d450b40e81c00014107500441d07424014480d20b045034102a0003560b2580e940640b0038402d981000b0b00801c02e01c81186072580c020b5001c02c0065402ca00c0a85400100d450400e10940c0302d401039200c0c41e6010b041c081900381c01c00034024180d85d4035488200713400044490034041904a88880c0c510190200002000100040701030b000a203030842c040e00849508411410000401070020b01000e441c00c19000720702980000e0301000c40e5003021811440352600d4802241911a0560240204100d440341150340f0500013208440402200c040c0ca44051812000c2e64203003000b880054103100082c0018050003042003803d9400600c51011100301504108401482c84d002e60b22000698000380240d030f88108032401003c2441d00c110400110000c2e450764040c0a030b014030b001660003a070340400041c1a2110005816007100340000780480b0302d24081c588140030707510a100c41070040c0c8980310340d00402401481524 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 159398767 1250 159397517 159397519
    0x312110c0a06020c010612050f0706110309090a180b060418020d061a0d03030204060206070e090f0c09060f1b030a0f0c020607081c1413020904080405091603051302 72
    0x311034078426072250000303074011040942155580f03080000d0001c1801c084c501000d84204040c1c0001041d182070310303085c60525030110041c809450b1418440080100c1169560300b0200d0b030110103501d8203c5000c000380401d2030303280c2c1d5800034020404e061000403618984a02000c0b03c061100c45035440c0810551000d0701c800039004088410040c001a2080d0004010110940e20a001800c807020004e9042c100100b402d5000c658005070910007594180309880d40301d445810520164100307840071404c0c8880041540641d140c1d0390010607107400b4508221080008014001500e410700680c000010354000701300400b89090b1800d01c0c4604103004416a2414092515071820007040118182d69107400448101d034402010401080000e103160058072440710080070030481d000820844c101242c01066030454012140c0007004002c1a0600a0500342e83d81900ea024403600c4600d04400030b070080e608900d90000005042004004000d82d400103041e0003a5000e1005840d00218103003407480d0300b2030207 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 159400017 1250 159398767 159398773
    0x9050705011d130e121b030715020c1c02102703050705030c0102030406060e0601020a0503030a090812010905100e0106021b1c0804150206160309020d060204030312110c 74
    0x150381a490700c040300600d8401d082502007516610140013900b0551185200e0103030701800f05600e68104c10208241a59905240080d45054283d840e60341c0680340503800f18819580020743c00b0010300742481080d803840c040f4459000c08407024640691540108107854803e00e1515803003003c03088850020400ca0742241d0a504a8100c407600c040343c1c542e04c1640300f0340303141c4801c000d82e4215007800d1004510450041500242690600350050000f0f90003030070060455029640340f500cc208040110398000c3d5200e10001545052450518441d01465060f8040150441c4c000a0305202c1f03904503a100b40114210000c00303940340c1c0160481720700c0a02807c4010390081a280d80c3c1003c0161120300d08801c01000d12500000303001c0140c005030852201160480c038049801c01080800080c0c111590b03400d40081e281510b4100003030924000f20088420805495918000946d02c3c1c801400482d290042000e5643e95100d003005803602c645040c003600303464500019042c0714040c0c1400e55002010501c06 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 159401267 1250 159400017 159400067
    0xb040618020a0203041707060e010f17100e0f091c0504090c0903050a03090e07020a0b0621061f06090b09011d10120e0606010203030708280905070501 66
    0x8054002d402c0641044254841000080b41c400c0040f820050b54010b580004c0080078281200201800012020b250512290807149428141c00c440c056940d520006400c42503940c0700c058808100706250311805115100c00180451500640c115502c907c0c2500129001d1020500e03449091083d0b060040340024424407040c450381c80107400844000010b8940488000c1c2c5031380310b55082c00542001140450442801000028002003c1c6503101034140094200400d540d180c103500303944d00602040c4140001e80c081d04035030304041600e44003504075030200d90491528100584607400d52410a201d052414440040c40e80c1c822221442a5042002da00303042000300300054a1501000d03640c4801094600c98400311500d680600680c15903840c2da0301c221501481c2d44480885006620241c00740d00603074104030642c0d800104694100c0b29034504880325035034640e80904040d056921a0883c450314584090100340076402c0020424011004e0303800041d5a40015500400d00c150342620703621518003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 159402517 1250 159401267 159401309
    0x606020a0b010b0a09151d040506060d020c03070f030c0302061b0a0507110411120f280e01060f090510080601120501020c07120c09020412080d0b150d0b0406 69
    0x30242100c4034a03410301e2070503551902400c00420581d46c0d281800210029801c07032000e00d210b0b000206600040c0c0d81044981852800701d4501c1c4254411340d001039800203815101d500e02003088070303032054000070034812280041ca002401c000c0c01c19000e50041c4a60f4022410040c1071007001d030b403501100c0140910380103014905661704e4110080984161112100455040e144c074000c2c4201148010810341d0b0b01c26a00c200d901450f9009060380080043d45801c1140001200c02c41d88614070366066040d0400e82a01c907920041c0c50740d00e80c004025420408006030b405094844441aa602c41c07006201665031304890781c84440c3d083c0700d44440341e8131160040002207900b4825400950096001500d08100c1a1143d8685141a84901d020707100488a910601c2545601a005000c0c0100150310b018030740303080b00240030860716014000034800a5140410440380c0d01410501d0b1b8040c0c140a8529004150007036690020503e9254081c1040d000c1c8509142070320803102680e030a840e034001c2e840d103045 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 159403767 1250 159402517 159402539
    0x1507020d091202030c12030307120b0a030b10030804060503012c1b040308030c0a0905061602010e0f03060f15040b010c0f030e090a02040810020403080304060509101406040606020a0b01 81
    0x40a81e018005c0c054034807034580710320041e5aa010b05010080d90781c3d042c03841c001408110351061032080d003840d2800d031807003a03694008254100c9401018103d41d80e216803020402d0f03900b0650000344801e00001d40001c41c0390304400694102e500700305036103100f914001c60241007030219a10781e07080128483e0015007194110b1108072414280d084286040544950b00c40e40c040e8401e03641c01509007804078080c42c0d519402580f51004d2b0000351103042c00c260f03154641a6000c00e604400a052104540c0700d01c0b030648609152207154000102100c0d42c50902c1c2e03001200d005000d880c480d01c4428521003044060415001708128600e0603075400c44024056100c020b0b4a460401044040100c0040713442180d6842c284a64051510342d40010b035a90f19051a10346080d03618510412158010300041005c16141001d40350700a8104a012070940c3c0c4500324079007492020309002400380e25100c8110b143c1c030b41c2010054800c52040d40c040280c15264a401d036980e06003114003e20030300c052001844416081 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 159405017 1250 159403767 159403799
    0xc120405100606030504020f010201060305071a160b0402040b0405090a0201111c021005160c0318030b0a06030203070f080c060c0109020306040f060b1909022a1507020d09 75
    0x40e405640881042600c1c1d00203484190780b0250009458905100540c50f0058460000e203a09000800a01d4031f1542c0322502d80f0028403580440c0410701c09002e04403403010301103402d0f11100c100c44682070103807480c00c82041e03981510300b81d01491070f00e821502c590500c0d114150060303900e00010143e4400d25801120248402c850210090184000c160300e103242d00d00041509044c1d030740151800c01002105441102c00040c220301c0752030803125036211101c3e00801040d41c0c040c2c240c130780008400480f0a9803400c4038120b0b44020700304181c80301000405207090384042c1c10389108400380c07001281d8910224000ca2454010003400d80c20118244c3c10500d0064010701d544000d0100104107a4090b800203804d00d0f404603400d40f440800181028104010303486507400b459000c40f0520304407000400800c2d0540114000d400146900142d014204071245040ba66450f18880c0e449500420760100c1d00d03200d0708804020036102c01031002048d0f00d6400413030081181d107402d50764038260314501081d01e5922690 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 159406267 1250 159405017 159405023
    0x170c010306240c0609030503090f0a02090403050f1903020405040b03010608030a0320280f02060406110c070b070302060108030313020402090a1e061b0b041104020f0d0501061202030c1204 82
    0x2d0b44080380025009001786038901d4020b894203516480c103425550f0a040118000751550f07080400032500686c0c0e024103207034000c0c0c1c142c90310039151071524400d41e00b5481000c60040ca003115078a0a00703102940b6030028001e4500544051088651686c18542a103d09000f090000d800904c0b10180c598402c0d03015001a01c485500070709110052081049150722444140038624100c0900001d41101071183c010343e810321786080c45914140e464001e484940c0904000c0c1031545490080400303100103070907183c03000048419140019075501d8610595400790004401600400c000000d20600c08001d81c0c0c07188441032000c2d0b03441603060b42003000075400f10000b00e030300110382900400d070428a000340850301440201030b44041410100d014005d03440b140b45c1010140d9010120b030000510101015400ca544500b1559a5079042400180a0301880221580761b000106525403c00c440b40c000c01e041300e1143d158050003100402801040c0d00c0111101d01035800d04110b0507000c11031009809a1141c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 159407517 1250 159406267 159406277
    0x402042402010902090a060603060e06030616020c0a060809010f11030411180f10080f101a0306040c0e07020303010617040312050a15050409020307230307170c01030624 74
    0x64103900003800e03401700350b0380c0c3c0700199a03640040c00302c10380511a15019081d159080c0c0c4032450003d001035030741c280040c8643c140c04d0590281815141c0200a235811040c0000c040d5030b0b98035258000244242c4084504083c80d6081607548440020380c0d203d0a20100c40701e195892859990792a5802c03400761080d0307040c0e013050b841c0e64141c0d4070600600c070540c000c580300e10303914180781803440c203d1095850381d0300440940d4010150700b5104240008000c010165440000704a0070015800305016101c0740300400d425000303038010041040f04080710041038507440481488681c50f514401c90381d0b40024042c8401141d90707240c1d002139154110944551082c420318021b8011500300a20f00203403541502c4030700041e0b0720b07021602200411200448050902543d04000811982c0c00081d17030b6540d180326103041510780499007461248100c483c26030f1038501904403414541d59102c0f220b14820240d41ca408180104443d16003558483d004413400c0742d1400c0c80301000c1e01c1894042080e06400700881d542808 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 159408767 1250 159407517 159407531
    0x50a050705032a060720070503030d0507110d0507030809100e0f010c0e0607060e07030803040b01050405060f150c030403141b27040f080d0501080705040204240201 72
    0x1e10400043c500514114210702c003c0940c8000350409a0804402d111140c01c84000c2081140d40281a910140c40620440380708048440840d4145a200e4209680600000401494241454024502030b006c40d9550211040d100da001c5503d404410700c01d40000703441045000c000c00d00c1840740c00d40002e404001d031010303140017207221001c582004240000310b0b0005005015040804e10508003230500c40c0c1852041400380400184080c85003a80040c035036035641e14a106091010480d4502071648140c1242e03990410b0304240400d0340003446007501c224189000503000d410a203200154041d0050981146500e1044c041840d58211081c0c0811601c000c1c04004041043c148040c190280e44001800c1a44a05144074820103044a400ea005002c02d000c0701301c0d02410810345c0340110980004510080c0c0b500c0ca00381c085880b8444001d407110b40c002c9581068491154420380c12a20000102c5112656840a200580c0601c0c402d41988003602421220300c2900c0400070850070a05100010342c00b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 159410017 1250 159408767 159408773
    0x3130f15050727050a050411210f01090b0607060e010e0a08070606050a0807030b0601050f03010806070f030b0105070201140d0203011e0b040320150d09110916050a0507 74
    0x5500846103400011030f0241c0c0801c1084603c04120100c8002d80010301c035440c00d01c0003080a01410b072080c2802a5540e0324260400480c42c0e003952101545034600c5005020041e0780f031100d15000b42c070006080341080000040398070552054150380da1028106a0424059403141c3e0020015081301d02055500d0720302d04d64079a4004d110008055102d0380041c3e4440c20213040003002c80344c0c0c54101d83e0050308140c5080c0403840c000117071403040301d60002d03522980d5601d08004843c14000d014601e610600040000700d1701207400f00e0f8440c410b0300d20360f40302050000d080074100c007610040716005d0b002c14010810700c4095441a01400b9440e00104000d510b003107452a01c8d5404c036402640485e504039a1400c03150390481c548159400140a001c1840c1e0809007591140c4a904109030605031400c0d241c403000d41801d0b100e4802100d80300b40f101046945948050786040081c155042080311110281d40c18000c0f1441e041c0030542c001c051120340c02074501034044003641e00380c0c8524894000d0090520040d400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 159411267 1250 159410017 159410021
    0xa0b07050703120c1a07021207060b030a0303060603180c05310207020a1406040b0a030917190507050c0603041505041b0e04030f0e010e040207060b120303130f15 71
    0xe400016940d013021240c183c00c0400035009840c09904420440c1c1003072003041c0d940022211019038401e451642e44210501c0c06000402d02c8200b2541c040c001e000030fa0f010f0540651040d403c072003d649040c04400da41040001c01c03d03083701c0300240b500e0b5034004240f00c107003452004010003810404c03e02010380910303c42030056a1522180c0a1529000580c8108505240c46040000d0040b100d4900035000c0c0c2400241d05405140921420041c01240107020f440c400c2c0c120f8180e86030400c0c01c94100701e030101110111648002d24031030120042501c201071148c4100101c61556030401c0c09008031410120400c41180c0c0040e109540610148820f503a2340943c41c450746004522590b4902d9031190903214031104260240d1180398205030642c00c0101094103c0c80e6101c0d112185d20340000004680001079a038003140d0001c0540203480403510b00704000303081e03001d6000c0300001ca4600c0d414a80070f410183e13592204035142031060451103a2800094a07401030252400d1140034400100071002001c881 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 159412517 1250 159411267 159411293
    0xf010501170d17070e0d140105090132090a02130608070b0a0e0d05030412050618030708180a03080d051603020903150603071a0c0c010804020a0b07050703 68
    0xc0c01016040d240800401c0412000004101c141040403035483e034846145203a00e801019001400310101c0740001c150760b40c80400c44103940c0702804110300d02c402c500d40c2d80200402c5071450701a604e08642007004030043c640c4c1e070035403d541c814036421003802415100300c11030002e86001c02610540c881c101c01617075400e99543d10503500d03604c001035580c0341104980c0707071054581c04050001d404020b00d44607942c0c4010030741000711050700d02004040c0246440e03859071003142d00510458006072150701c20444049446802950802c5d0004144205192120b40300e1180301e00003070034150704111415509500c1000c00d89056001401c0c1070390740c0e0b80c98560603000d500607450741c0d07030ba50f0391071081200182c5100703602d080d401a1454218100032042002c00c1d0349040900c0500d11340b4001070001f501550b020000480980030706140e01c144265a030035901d076541c0090a20901c680504203101b0707007952080c681144900d800420f0031082c603246c0100110700c1d03403003080152003d019188001c8045041007003841 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 159413767 1250 159412517 159412529
    0x209030f0d0801090b0a03060903020a081b060603030301080312070504091803020d140f070206070f1a0a020309070b07020f090106080a062114030d09031e030209130e0f010501 77
    0x10040c580d140e04002d05032107058004250389440c1c60008982a2500d04d203600903241e00c04000103541c4d50b20304040e4600200481c00504901000034960080714100100020403a0035008071007994496408050300d900003401488071951043c41001001c0d40b50401031500700e001400c0240c40c191b1a5407506081c0d624520b5040b1048070a401e8440405904012050008000386402e1030a0011103c680c0c0407031268070b4680180c41c3d004180d010555650034211044036902c03915040c60307440d85146c01d590070001800041c1d03580400c040040d440b60550700842e8456525040035080c0d160415003600401c0d0060b800681e00240700c1d21089481c0c3e101c00b08000d01a0039151988025403034500035950550741c10744c0009406c000009002a00649112960691264452480704140f14118441c41c5140100703030340c8241c011f06000b6880c040c143c11a040c14060840c20701e0300010030000d00019010b80c4688000c0c41d4003d0400007104200740202e900410060300a4800d594042c0441a032241c00c4d070354283c03c04 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 159415017 1250 159413767 159413773
    0x409020d121e0c141b010807030209090108010e07060503070203070605070912050f100204061407031803120305060103060531020a020303061207031707051005070c05010c0306081f0209030f 83
    0x12042c0000c208040450507a0000100040c45e5000c007071704040000c025466043c4220000840c0c96070340660181c600000000d00421095079680b403141e40a80700755100034400e801030000106200344614122403186e421900114074240d900e40e503090007064010542810070240703860101e50407040b0b207150362159018100812060781c04481a90a10b582401d14404143c030402c0700300a500c0d0444214103001050801c95921036030704e800d00b0345042514610041ca00d02a07502c0210400086403d5019000e206603020007803a038034040154112803160140550001c020110759010360a652035500d6a01cbc1c4450400c20350003d4848401c0c02e9800042c205c00140c1c001008100a5040154100c641c02d1001d030024040503185448034041551121543d071000781001030880280502000b00003468a0740c08000c200c68904941c006180d8031114204454030f5081a0051101c1c0703109002e0201558200130252208201c6c184202c0c03c803144640381c2e80d0901d03070240643c0049541c1802400301110b034078009 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 159416267 1250 159415017 159415037
    0x9140f090c160f030e04110a0207140a090e060a0c0801030c03020906031216050c0a0e180a17040608100e0105060c0c030d05030708070201060602030a0507020303090d03030605030c0409020d121e 85
    0x1004140d59142c134440d8007d40d0103000204900342d0000c1e0400485041e51510002460441c01041c41e204181d0403a02c000750400d01150015440003507990300c6190f0710b0004003d40386181404450214080c40301500340c2000440034005440d00201795604101c00808980c034900403e81403481b0b0f5003099001421000c11343e800300d8284402800041100002201c010040034242100c503001c1d45070140040c10401426240e1044a1104210040704160031800306040e9850a50900b0707180d40c094024040041d8015021440a100800c6484140c8601c0c02c95006140e003000c0038001c0e10307000140c0101a622030b0002d04460f60310240b15443c9200e11666605540745003807540a85512805080c01045a1401804000040c0d0201c1942c03406502490b02540d00c0400c2d000003855806101051980040e0b00f1078400109a09503028400300c032009d4055400c02c0c146c2c00300b04400c071600c840c4043e4118a2240c521000158614403194021000342401c0c0c2100c090209a144075800e15203000020030300942c5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 159417517 1250 159416267 159416269
    0x160c0602070503030f0706110f03011401032a0f030605190303020c01020708071406070803090714121506030a0f2f0105070605042109140f090c160f030e 67
    0x111041c040c0005400070740c500a40810762041c2031007880c4001d0400d543c0c4110380800c100420040303400a030280c1901c00e0300c958603260051306104a854405020074905100000c10520785103800c1e4505601400c5001c1e4982840c03026900e40c41c08070618810155910004110f0355a0303503500c5080c440c45808114802801c0d4a0042e181003104040c080c10355201402c03c000801002548005440b0302c04102c0c801808903001107400d0340544c5400500101d804010070032414000a0f07210121008240c4c08407030380b044402842200d80c064050340004c0c1e04100001e06591a20301422500a030010381200d001d140c039502d440861503d4400c044808203505e01c0000f18106c810340901c01d10312041403660b4241a2030130000780c01480b0b541001030490741c8690000e010710407030542000e40300c0d040401c00c2e004210245002425a41c0710b00030b0090f007145a60404200d4148588000ca96040142c9241c40b5900c03419840712003500031241c0b41c0390f081c45521a210004810070324440381e086c401d03100c1d001e00c208108 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 159418767 1250 159417517 159417523
    0x6051003060b0a050a050d050a0912090f0e0903040905010b030f060618091905011403071a03012304110712020c01020c0d0204090f030503190207020a0b0a0203160c0602 74
    0x11120010542080428071400500b48225040c09415013415607440b00c032100103540301c0c040d009215004526110400580038150380003030690f035200e2100042000340301c00c8107880d140a00d000c0c0d03405d1660303032200500c0001490021950809001c90407a41003c0e602c40d80b413000d0703c074242c0203444140c802000740b019072040c0a043d0b68220707000f20303699803e0008906001c0040e0387c5105ca513a210304001400300307105403000f040001031005081c2003405075684a07600750070700c51009200a4040d2040050008109036208030807540780808002041c03450f4642000d50354101c039000300310780d5401c4d40340d504004165618818180020010312517030343c03242103500304111005e0600d0100019500010040c120f1aa808555640d00040c120b4007051000082c1c00800d0040c120307644020400071520110701d080c1a0043c0c0030b90300c50300b00442e4801489440e2800c980a070700880300025000442c80303106001034101d0742c0180c0003900b01031044a0500728209040c0c1c4611118003000d032509000e404060284903418 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 159420017 1250 159418767 159418789
    0xc020a08100e1c0206060409260306030d05160209190f0c14030907090e01090501140604061d010323010903030c03050a0903051602180403030b030c010c0b04030e220605 74
    0x3083d441c603003841c0c401c1c50203501d4940080103984120356891a00040103100341e255010b1401c1c542c2007440711031090707100000b2039205450300d80c07080c82030401121105104404480c444004654640210265030303081c02002440500403512582c01000d0724181c91080c4d101d04a0310b05041e900114808072065005000c0e41c0401d100c041c201c2504100304600c824001403c002124142d0030300152203031254000500505009200602039400c252100034078069022045012340000c40e003c11072160386290303142c5000400704442c4e0036843c1030b40041000c29003901c0c05114040c01601c2126012044403051401c4850700c00c4120701080e0303a4140c000c0000d03494032600b60702a1846004000b6400c843d03e01600500811008485040140c400d03030045482c1c402d41d20000401c85040101c440c201450041c000d00030012146009100300c10b6000400c0d071203414400744464001c1511841d58a0359182240e004048505e8660003400b00c030308810307521680b5403c4503407140402d130740081d01c0390401003000f00100b50 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 159421267 1250 159420017 159420043
    0x9090a0c26060d1518021f0c1509020901180c020303060a0302040213080303070914030d0503060904030c0210020a05061b160c030c0902190215070c020a08100e 70
    0x751040754010300c00c2901d03501c0d0480c404803550b5001c55854035001c1081180500b44280300f505021902d00768a103450702c185560f6208445490b40050030313800f103060b225445010440083da280d03a81b10040380c01c902c05841e40a15421002c1000c11898020428508007031f03009100710b802c00400100761120a108641c4219050701c00f861850034a200058000030181c00013900c540d60003c0d14401007056507031a01c1c0201082016a51680341080d4040d100d14001e10603020104c0c1d6401c2d06100500c0e000c1950b0070051000c1c0c40e0310f1b0954540702d0a0102503034008004a05200c020209640903a407403201034074540030321303600620b4039101c5d030300d407460800318040c0c50b031000c40341c80015a141001c01541a00d4100c1c1d03090000070030380c14036403c060380d00108030351010f469411040c1020916003050b800815500084171661800c105010310100d0b600d2801c904030310528034009002c41c1d80349105040354400180010810aa1540c541040c00d080c540380c1030000300ac05549401c134418142050000e5000892 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 159422517 1250 159421267 159421307
    0x10b0c0607021b120a12020c150f030c21041113050603070506070519110406061805040b0301020714010606090e010b030f070903050f0f060c09032109090a0c 69
    0x2810a01200c5445440c000f54032840011005005900c0c00700241d5500c039401201c0ca04d4a4400400d019446902c5400c0303036401140b000d400c190341d114200c0c0c211038850392074020700d0f4510761321003840045a0300710350b440350527403482541404000b403c46419103003e28015000f603000010085c04014031041000c590820032400c0c88100249a60085055011110181e5440d541d0341603d1401605090f400010501001c3c4003000a0041c00310740d882e0501c0948054500b04001c94881c40f042d1000300b01200d1845c03c00720780500c24445410280c11001301024040d00150401040b90f84001c0c1040355041140116075641c601004415482100c0100030440000707000741c0c0354100800000d40d484001d00e1140003178191008175400501c078409203801180c020381a502452078500c0c0792910b9000c21140b10100b0701c40d80000c505950035240887c2d09901d002001030a401361141d460b40003c1490309181d109042003804429041c0e142d003a1720074407400d803601c6c001601346d00c03510000d01400c1003000b80d460440 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 159423767 1250 159422517 159422533
    0x6050105070b070e030d1701060305090606041e0c05070b0f07052d0309010c08060f01121e0603080c07080a020603010905040c03020303040602030409060b07030c0209041406010b0c060702 82
    0x290300102158195a0031000c040b8156403440020f48070f807884008496094403c0c0500381955039480003022911065400c1c4208031640c0c2c510044080c0c82d03040d11003041d80d82001c2c021403190f107805e500c01c0c03503003001903810f00f05000501484c250855500805407804074000042c42070401c6041c16071141d0084030103d204441e824622001421401818000135103580c16103600c48009640451910404a8030410280c0c2d82c941800101e003c0c0c5420340e440408545070b80d01107445807070300e07803401c8a1070007040e960000302500c990907a401410180c1d104444031170504c000c0041002e60350107031102460051040c0b6584a02201e40f1610304090f43d80280745640040c40f400005a40b80000c0780d044030565400856143c44a040168141311990300013940351000040024000c2d4000c00903008482521a08001203981c0d040c5000d1180b0070380d44003c00117091000203400504e400161039401c180145c5094524809803105a880d20780280c21800b004100072031130081042d4100481e0340c2c844118030142c020300c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 159425017 1250 159423767 159423769
    0x115060e18010b04050d0c03240e0106080c011409190810140c0d180b0106090501080112080a211a0103020c300d200c10050a020d020307020705040b040605 68
    0x10740100e0140512586d000858002405200e180f11005550808100e004090501204000d402c3c0001000c030901400c2c0200d100440c2d1040c45090308983c516070140100349581d50044a1001024600c10361007207043c000c052140c0c81e088101c02240c5013040f0b280c6506410801494036200d0080c0c0a1809a03040454060b0042050a03078560003018074903480c3d803a00c204c2c494240180210f01405010313103480d00078000920100c6c0000c2070403260607440b2038030340c0f07a10f030b000446484109009078050305c50001d40d4100091340070b80c02480040720070b2a04801d0b0300da40c0281e034041c450f26005101e44081c0c403100d0840105620f02d8000c02d580300d0909007185050741911003a0b88400381480c0e020300b50042e0202c41820042002407051003105920303091a65074401120320801422400990640c020b0034140000d0300d443c030b01d0b04a030030f040c0038070008100c2218421142009040000c0006c90751079028411b0408030403560000d18019111a00604200c5040c10f0611003202c045040d068030542c03c0400801c01 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 159426267 1250 159425017 159425039
    0x130e060f09031305011d040c0c170406080c07022110060902070203101e060b1306020c01080a0e031c050f1b0717090a060801080f060403080f04050115060e1801 70
    0x1290002c1c01c0c20b204e15000800c4018801c81c40e800706c40c1e041814101011300030390f4400d9956202c44d2241000b6003900010624a0810707004034052200400e5000d00400c00c803100310009010418030051000c0b101555000d5102c4d10f07050a00c10803600c3c0da11125424a4043c198080d6001418a10380700714100780464001940e600d031803611500c14075030351310b00004940000f81000500034200b2401071204ac0da0701d40440006500c000800000c82e00034070b10200303900d8070100e01411a01c0c0142d540102c59150300c44003500421030fa150200d10780c4405c20440d0801c1441070034213404407113040000660b40c40c02c030750555480180106104400b101c0103203805560b600391015a0000c41c0c0000c1c1b00000301d00b40300d0300b032120340c842c1100c050380c40401c00c900000c200741d0188081d030580e0207520641d856010304210650b45c4640646001b008203018000081e0002e400c044031a40c480d00a8002244410044c1051082031581d60800740028100342000800c40c24401c000c1141c5403290345c60f8000315803410b40807481d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 159427517 1250 159426267 159426269
    0xa0f030305040c0e07090501090801052a04031e020306151003020d020409090b100e04020604050f0402160521070c0605070302032203020109080d0914130e060f090313 73
    0x400d0560380e901180038010b00c0c80145001d80149012090f036030810b604003034801c11003441040d0008a0f40c800100700d2a406000701e030b008035011101c1881c050260782e200c126440030051251070340b220030720001001c10300502d1510404900c0c8101a00d000b81c1703a00501d070a04000901d010044d80000002500944400a01c00c01000c054500103880301030100c0040080c0c42150b0141000303605044816051110b0801c05038022840c80700442106660350400030000c0c00200c50283d4400424041007001e4100b1400c2c84640c1e0304010001490001c941089480b00d1240c4981070710b056114070041070800e58104100c034091000d500d0014180801581c40300220525405042c08014000c90010200f50080090310074503550b442e003405c0c16202c4000700500b080a00c0c40280d0020b1031101000591060110344555181d040c1d9642115190400c0301c0e070340203241d810301840cad00011200d4840c440701080e403144d03c2e001c841c0c18010f03000701c2c00c2c16461414240c0005d0f0040c030710768104120344290611880300030b43c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 159428767 1250 159427517 159427523
    0xd02030f0a021608090312030103120f0c0812040602040905090615010c15180c06020607030f060602060a0b151c05070504050a120503040321120b0117150301140a0c020a0f 75
    0x95a585c1c540030220781081007804942c805403c02000200400c580e5032843c02984040790388540d008110801c0842d0041e40e81c45014140200404c007441895025005880c0e01a00035140580303810395460300801180c00860341d0740e51603001001840041c1e01c03200b81c0c66200d0030b0300740fa0000c0c1c025029211408050300400310540459910025050700c0990003849105154000c002c0344100c0c0c2c0d54000c00307034072990b0840d6040000ba00e800c02020103e0724900c1000c0070358100303500408290b5078004d12180189082221039074461541011810500001e0005211403500140280c803910405007010f4191200a04410f051010510007070044d40c41d2030162904035003031f019815450019500b002400c610960b00054a85611203443e040140000e6a100c0a90003599507822203c0003a00c02c200b08460482e8040c030b00248101e4410f1440c0c03801400c3e23040e04240052548010b5051000000b82190040c100b510003504032201080b98100843c0b05049910801e07002411400308076550315000c04505000c01 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 159430017 1250 159428767 159428783
    0x212030406171305010e1005010e040b04110f0a0b070b0c041d0a0908070605090c010908060a0c170106200703050c280b131e060516080d02030f0a0216 66
    0x114542c01d8000b007042569003280c02042080000c0c00c60f1901e846c1088101f141440c1020000205444001c010610075a08440701420035104d80e526040385489a440d115408521300703140b01856079501e0009001001d00120499a449152401541c8814014002d000b009000e2100300034a440d00c80e03034405000c07000d205a288035511414001c0040c5141080a011b134800403c5500c100807040d071040f406103030300328121040c0340d1082d80111510051030190341902e03040980850f40c95001900700100140c51400d00c82200c40011300c440c024020264001400600d1b003450005280000445807416450024080c114250071030701d421b0313035450000d9101030080103008400d000c0401140c80d040d14620300e621841156039602c3c0d0015101ea0800ca04d01d46190a00100005042c50b418891010040003915010111890004241c0e2143c010355200101d4002c4510810001494803004200c08a49100300688a0609041030102414018000c03500075204202d8100398461a460603801c803607004440d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 159431267 1250 159430017 159430021
    0x1403071809020a120515060f0a03032001050a02041401140f070c05030d030e0d020309010206010b070204150f0303022a04050901060f06020303090c0a05010c030507060b0607050a021203040617 84
    0x11820241540d40b104d0354881c029802d6608208000c20703010503085680701c200904d522400f040181c003180d9050100c1c1e0100d40c8820800003e40a00000c8803000c036841182001c07041c55091b02400d40b142164002d401c00d43c00a000d120861a00c04a400c070f41c2800e2801e00d50780311401e8103041c82c91161032400c111013480840e0890030052054100d4000c1c3c480070b41514125080c10401030040c2100b850000110300030301d13100b031464510020640d000e07198140e000303100036441c0a00d200c80c554072052041c2c0c0c0060700c035610b02682c4c080c22540e18009001101d41141918558207000b0b042560044070002c0c01c203541c125604151090f0b130002010701504480016041d103521850341d00610480e8041e58201640060010300950040091841128480c00350750455980004002c102100c41c020303140072070303880212400803d11803c040d0080702d100368000a0340100341d0002420b641c00a10040f522540415007103000c42c00e108800161501c4960f00940c181030800d5006010403c201c0301440c014400100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 159432517 1250 159431267 159431269
    0x50a0c0b150604150f05090303070f060e0303010e150a0605091c02100f090504050402010503010e090102070b15010314010b1605031c0203060909060603060a2a09140307180902 77
    0x48400260440200400c0e6625504e41a0002941141c65070501103481c425120018500030001c4881c01d0000030055441d01549030b070f0303549910030744160984101e40c0c1c4e072075003c248903030410045002c1d1107180c201d980c503490490358142d029410a0600340c001c1810342c034200a555000703401d0310020700b401c45000021481d0541809045501e060029500180b10f10000c00003035001519050021850b41d51030a845842e0805d21040d104187c42c001d001400410040000c0490314030711a400c40700300320000d490f008054903400009002625408018140b4807005d103071540c0c152003402c0200400f0000300d10b05615225203018640504a480900000280140c008022040c0100c80c14400e05110620565052010f004004e41085441324080c08503040451074002d80001c600d403044c0c00050040420b0f5030364041080c080e08080022a00b2400720100c0c0b00217000b0a400d21b40030032085030381d510f558203140111401a840703980c010280a03801014040c003055041ea4804d10300f002048501280d5555644 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 159433767 1250 159432517 159432541
    0x1706010e09100c050a110c0f0d0305040f0b180102010509071403031b0a03020c03070e04030e060f0d0b0415030503040e100e010f050a05100518010905030a050c030d050a0c0b 76
    0x41000b624585880210001180c02802414044400d942c440c0480a91505019522200300d019151f0001a566034002180382c144003940841748039180890034603036039180e1003c0c80841078100340022840894940800001c14495501d040003d10090002e410f050306ea40303880e0b03000c1d0b000c0d03500d00812803240100151000c0044580e1120000c21411044c20000c00071174172441d03c0a030440050042468202d0a45400500e050a5600f0680101c015488a41c0d00b80c0f00780303580341341d8250401428040000c4080109020b031a0124020340086001d5000700200803c423100350f5034040c01524107c0060000c00c100005880c1075030407114000d0440e44881d070340600c0300c00007540212100b14114002046410104e203103101110f000f62202645182c590041107910700046030b01c58005031083c03048049050345c00b19401c05071714040c14121521500e41004c642001905081a9540d50180039281e0043c00c1c1003003c1002c8601d649802d0f41080a03094004003603084400c406800c5144000109084000030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 159435017 1250 159433767 159433783
    0x23040506041203230913270b061909051b0a030504171809040f05160303020f010c2f0d030b1302091c03090b040f08060a061523130305071706010e09 65
    0x41e00c10b882c4d03c1c00402c01461f030390350901c01c100c511040070307004100301303007810000f541040074030403900a060b034100012440180310080400480e41d0010108021340c401c0c22009182035545035801060720302d0a0304043e485400d0700081c0e08040c09041040c141d006141041c20000ca100407100a00c1a4486080001d24040d1650303028089000d04001d500b118244066550200d07442602680c50305200207807058201d0700c148000101003540341c0c00040c00281c2d014071102000c5122241d4220315800300030018940403550000306c012a9807255901550b2400941003010705949020562525829001207082c0c0c000940c8400302220700501003104042c010f1200724080d043e484039141d12180d503042c1b07594842d00e81c3c0c402d4203034500500d000304a402541e40a50001d481d40c0d030031182d030317603410103d021502018008413a01a1130b0680c0350400c0d2144100008003103040400c00c0c6e00400c0c4c2d00b1800c03c0b0f0706082c950307071128480303a1082101103200c401c0410a141110742038940d0b0705003541c0361b015203070a100c10 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 159436267 1250 159435017 159435041
    0x3060501060309200a0302060703030906050702071d091209120a08090f030c1f0908030d0608070b041d04290106020c030304030323040506041203230913 67
    0x240000824a980d055110308000340c040d41800709041881c804c148945044000440d0700320001c00c0c418805414500003c2001030321034600080d21a0294644400f03c1304140d42c4000180c204150410080f40c0c0c0c03030b00386030410444000700c41c10383c01d003023409035038a08120380c860101300400300720b06506035561455044a06105815954055103915100c0e805a000122603440f56003c0d40161190b070800143d40040104007904038a10440e50b41140912486803510920420200f480c012039440800d00181800e034800740008580503082070503ca083c88100d810480715260140010400f4103101c5080701d040d02c5014444000c181c6660508240c0040140184a0040e2804414890520020078800e040343c00640c00d07a100321010000301a2248034030720004e030000388504400891401c4001403564544541d034542d5144c5a03585002c140f00c1d4005034440c2541c0a0b9164900c818143c21411603030084c3c08101c0f98901c1d140710018901400c0c054130540d00c2c040c017100c503803c018010442c1d014140c034042d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 159437517 1250 159436267 159436271
    0xf090c06180e04031106040506041703090a060e0f1608010f051902090103180f060c020d022505030f0604060c08040305040b0903070f1401020f010209030d080702070b030a020406020c0d0203030901180306 89
    0x14041c1441075807040d01f654111980c071034bc07401d100c400c5c1c1c1e64842600d000e43e20000150400303c0c240d4848a010b000c000c10200340328000e051483c116040304012404071001202c2609460b207283c00740950840310601208940a404c1c90100020340f0f40a03821981c890000120045c0c891104500403001010802c0740301602c16405a511424000d40510b0712401170710400041c031140948040490720340071100341c0a00541d001c0709440b24065090315041408100000620001c0d581d1003000a192000700e400305480c9402034002d200031710445014109011249041220f441c1c00d00740d030001c015100d2413242c1c202d1001e006c158580207070780500c0210001c00e540a030f0300c035107240c446a4941c0070b800b40c110100c5c058801c0401d00d400d03400041c0240c400741440100070309104510b1081c16616514014840000c60040040c00704102191402840c001c4010400041c6c03640e0501e14041e1402844507070440c481c1a5a13403100700143d80000c201c0e24007820038a020700454408203a00d0018041542004010034 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 159438767 1250 159437517 159437521
    0x3070c0f0602130f03021c030e010c1106030115180b0a0c05010e060a0b040b15180a08010e030a140903070612020708160b0c070b060f010c060f090c06180e04031106 72
    0x502139100090b40d00844400c410007041044071500040b83c040018041042c4020000c260f60241003014000d030b0190060f5071505d1134540001c1e419a1098001c41c10805c10210034542c041d91100d0200c3d1110f0b4110049281241424401d0b199805801508010003018072208020020f003034100d400540031000464407a03043c180da159019002c09012140681e141035440341191600e101d81035109010401180e140600c0241721a40080004481070f0b000400d216000610071381c24407441038050580009582c541d056403000078000d40300d207041400e00c0c003401d009010f00c0b0346e804580c05c8210b9002d800c0400c0c921002410580180c0070b500005400f0303000c040b411003041105c0e0a40040d055200d500401d85070350390000581c03118001e400000c2c0c104c01c90040050003604014805146411050500d03000c408520354a0205a0321820040d0703030441e488880c00d00030000350301d6410014020350f04000411050100c0203480c6c01e68144944070f10496044049414140a1040c4c02603052008003a14003034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 159440017 1250 159438767 159438779
    0x11180406231630020a140a05040306060b0405061902010e0a030908070b0c07060f0e0d0615050301052406390a0c060302070c050301051006020606040203070c0f060213 73
    0x4018903248041c0800c107040c1904002140310003141c03c6036a820000b01540c48004003182d4002d4000ba0501c10901a02c20130580a050329100500080f415543d61030313644a045103050800c0c1d42ca154442c01640d07100740b100f8880ca035100350948042102c10301e041c042d1316408070000c0740500400550000240204080070040c5035005c0303500001d0740c1c106001c4840090380c0702850412480b403080410f01c10f13007101d84240b040511940000306681281d01e04074a030302c01c00c44002006680c407104115442d82e91041076165408641d09001c004082c110002c018901d000c071018100803284102c100114504030105403415580c90b010340d0029014088c1b0b004178034032101d00b44051480c3c081d030300c01d0081e0215403004014040c00103c240d100c560115002040b00e02d440d10540c081d401c0204100d8030031480e6030b0041000d0320b003446410721507c8203c000301d0140d03150000c003a0130203a0182006028038010001c10130110f0f040481c941c9602e42c44000c0c0020318289042950090081c5240e000d01c030420701d5400150 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 159441267 1250 159440017 159440041
    0x40b040f0b030f06041a0702031306030603021f0801140402070501020a08100b030103121101022b110f070305090111070801091a0708010501030e01060b161118040623 73
    0x10740c62080e8120744004001e09001652510101e0703004121001c40140200869060811160003032a140101ca0a0030501c0020182d4400c0c1e60700407000296480b241001546484424800c1c48110760044001c0441030100081c080c00d814003030007068a11030400c0c2605030f169a8129941c20340c2110085441c1c420388200202144030075121206601000c240109024a403076003224102c0c0d9009900e020034428102054841a021100590140d58284490b84100c000011000c1002200200c3d841440e01c1d0708000034225544044508006441844686c1c2402c48610445071031640604003241c41d80c5032440100d070405030004c41010a07010f04080020400c0c1d054003c03003185407182902d80050310b98080c90f040880d00c115081800600c07903800400540d4001da2140b1060702006001140c816181d0b0124401279100162003043c4010b515072100030301481604982c54000200c91007600400ca591705c0c102680400741010340096a682c0228440e910003000400000c070101c580703003400c4c0c5003d0304000701d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 159442517 1250 159441267 159441281
    0x60306010b0a1215030b1602330f070909021303020415051203040609060302030c0901110f011d010501050303120a0507031d0109020112060503070b030901060305070e180105060a050906040b040f 85
    0x30300c08606d400803c098104004420220b800302c5d5000b4640c1044421002512092060700e440e014a0109034801207660032000d803501c21428140d080d0300a04100c04001c005e045140d1100c03010b03910502c0058240441d114481d0100d0341c04880101f0a1040c020200741c034031400b035100d5684110b80c900510383c494004000341c81102c080d6102c91a60b035644010680c140e1108172110100424204010b040542c00b0b03481130710560b01c6400071180340303030b208800e41400c54241240300c81d0342c51406248030300099802d002d0301d0701614094000d18144060f800c081111603401403c10a6030545500001303031918400c0d030141c030301070301b6a503d907006440805072818001c00320b003107050340040c40850034140014802d000d2041100c2015000b8103141e45044407444407500003600c800400d5481d40e00000203e902082444007070401c00c40340c10b4950418810381040304200e00f21111580e4100303010820f082e90340c01d07200d00403035009072000d00042d5144c400080040041c0c8442d42e901c189080e030aa1015102c1361b100b40 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 159443767 1250 159442517 159442523
    0x902072a09060f06080c0307030608010c030204140a03030801210c060305061309020603130812090708160f0b07060b100f0908010e060105100c0b010b091305060306010b0a121503 78
    0x1415141c0d000a80a50f50074000c0c0408200c0c518086042d0b030050034002d40e8402202e00d0000381290b00c2c1e0401c0c5e401d503541e540485001030b03000308041c05035004030f034003c095000e8101c582c05496482c5507405400c0403414490794038503a901500c4c0541a0031920074002c11a0f610180b80040b0980721980070380203140603650b0b98081c0400c0c42ca40c107000c040d1072050500361a00101040d00b5070340c4003130318a06241c690100848148000b400100e00f19920b10032094003c044000c041c1a0050074450709603d040f035642126565841513000c200007000a8900b404251456421420742d15051800c0c02c402500034900100e0b00460002038641c181e661111f26900e05501598607003284560f540c0c250390a8880000640319280c00680040000e89003c0c10780c03d45c0a0840e0800d4400e0341d03195180c3c405064400d03030047c2003800b00040e21002d6490840d60385040f00001000410070743c1441d50210355226814002c01c541913600103103810b0058010300e460000080b5245081c0102ea040c46410038203804148011 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 159445017 1250 159443767 159443771
    0x5070305010e04050703020f1306030b04111519090509040506060f010918020a140d020d1b0c0f020301061a04140a0b0f03040f15020c1006050303040902072a09 70
    0x802c680100c40501070040d90048020001c6500759000c0002500b0450100ca0784002c805d82100c20590440c0a04c2c2c3c020760040840c0c4c0384074541820055070012407844030354410135130076160b08142250103003600c0c000503c00d0002c2800003a06030043d00c0300d40f05a00450392141c08201004100540000d2303503407190f5401e4a40c4c2e00346402c02c200641c0c052074180900d60031403800c4101072145450590182440c0c01c014685904903503028004081254001150305244903000208126403407503d008518002c110001c54a1104426550003040300078440002420302200c22030f198299502508100c018001d10120300002c107600f06101e003400c2c0d03c1032080400140c00c49900003114542080c0040465201c2902c0c1460702e0760025604149601c0107004035001004211400003141c00d040f114000b0303140005005a60704c441e155032629100002c2c06c00c10340300f802c106091000303450110585017115600c0e0000b6840d51414606228840c0e44519000d00840300d040f4400305240507441c0400498040c0c0c441 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 159446267 1250 159445017 159445019
    0xa0201140105150c2503050706080606270916090b0403030203031810020307080411030a032a140d090605030c0f0703031e020405030d0806090403030b03070f03060507030501 76
    0xc0224240001d00c5500e5000440701c60440a071202040140110401e400544845c05000c58400c141d110b03603949031240d100b001803810700c1000003c100354005000b89042403d103624003203000880714030038690300c0318680b03101c15a1500c4a441d020204041580c004000f500301e0310307001e0070b1807101c402e4600b40c00000901080001403404080421107081d41c0d015405180303981e58040e01e400c203804820440004c14480e80c0c1c1182138456030762011310b01403120f079070b100c0c4401d040c07034280281d14440c40d010300791181e04003034a182c00294220640b881c2000c00b80030f0108031000010011100c00072154000760003580000349e498000c2d000422070f001c0d02e00b040c2c0c81e5060000e840d4102210680005c035031107080c20000700f00640c0c501e00b02101601c1d0a074032074540414046510050746006242d4030b00303400c03251074011070144468501444601c03214a02441c1060a5144c60b10002e0004c50014101405155036801545910b4405000480c007400106810311800c550780d10340200100310841e0118006072410300 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 159447517 1250 159446267 159446291
    0x2010c0c0510050c070c1404052206051f03050607081e01060509150a02060402040b040b010e0409020609120d120b06030402010f031815060b0406090b0315150a0201 72
    0x889100d156040802840c40300e400800c2c641c01403201400411440b00c00788007860000320110314007000f820340041445031703e1b24075405000548001030140098400e0f07144041c41c40094148043c0c2c4180c0c0c014802050b06c0d1690482c61310b0458900040f40300c040f080310404030500030b000482c41c0c0104242c1e52204042e5036240c0c0c07585200c50340e010710113030000c041d00c004004a5118038007078040107c0060100e42c1501d17050303080c01100d130b100591250140e00003004100035071806205220005409440a014003070110300000d02000c1c400302903a11956403030110f6429901d5210581d64200342c0901030820441141604542d1100c504180790002150980345000c40c541c140030305003600002410003030030b5880c0c3c1d500554809071500c03030340c40c1007540d104420301805c2a103001142c8600c2c00382040125944162941c81e040c0c030041d4012900c1e8080800040083c41c1d071060f031144c1250301d0a0002910380d10341c1f03070404c04002202140b465024850301512054940c1d11401030a40c41c14039002040b41c1074444d2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 159448767 1250 159447517 159447527
    0x708090f01050333100c03080c1e030405010b060f1305060a0917010b0910030204061401020c061b03070c090f0c050306040c1404030b01030c0e090c0d050a0f050d02010c 74
    0x3200109103040c010b0703013110030201e4000c2c240310101c0c0110000c4803841108000c100f51400201546000460700c01989040c035801a00082d040000d420b541c0c1c4c070700960340c512141c5840c03c1d40001e107000c550020016040c0a020340c06484801e00044c6090703030310022a03902c1c9640341c1104082145412820f000014146014421075008809948540f2010380c80c02c1c41c05601c4654040d1019076654a90380894025a83c04078140d00c00c1c00040c4120313103241e003980184000c131038041c0c000400400306280c2a20440e81c0010304040300e4107080f45c0e120780d6903000c0d4015620448411002c02c8440c4401f0a40318100080c400b0300e81d09903600c3c00c00c1000040e518141540a46015015810100f0b0b01040416000d04080d0000d08452020b420880d500039507509203000642d20270750044da038882c410801402040408a00c0d00b00804035004c112040d03041c40304109480341009081244500d04400041040080601804506607003248007080d40914a041c916206c0c10101485401075180030b1103e00194011 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 159450017 1250 159448767 159448771
    0xd1508011a04050406020903010912020c04020322080c01020301141302070f06050a09020303040308090906010c051c0306090f1a0109030305030604050a1d0703050607090e1501050d020708090f010503 87
    0x41c0c14440880c41801404001c0c02c0141003907400507001c0000782400e441c24040c60401c3c0d446a03c4400d2a50b5a41d2002810800c031901001d110314010028000007400000302c035030200c0a001c80707a4400a11a03e4164964400d03003000d400903500100c00001c0c0d05011a114420440301074a0f81c1c034001c04c0480c1080d00328443d005c0c0c0100008520408170012841640c8426407014656400098140480e000286560443c2c2d00c00c0b60000c0002030811340078104a5442508107000b0300f05a0728125aa40e521030b00e03800219000891460341c512181c031421710030b800040080c010b401c004c0241d4040b000b00b850182c018000e09032183d110025110341c1070b502c100c402c0741c1201e402d1790703607141103481d00c1c070030080501400f42003a5019516440103011201110141092a54141008200507443c51030f080781095001814102070058484041100a440d032900c5544401d0a404800005201000503144c03401040781c4c181055201003041820882c10000801c03124404903809010002d032000112054802 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 159451267 1250 159450017 159450041
    0x20d0b06130615200a050705180601050a03020f04050d030f110c03030406050904060b0406050304050616120c090308160605010b0c0c060a020114190c031b0c020f03030d150801 77
    0x240c0f8074828140d610859100c8042500661a149240c11040c1402c0c40c04500b10700686030343d00301607000c029510b0003010500c1409840c128000c0e440ca0131800282460207100244e000b4035070005691325100101801300e8014080081000030001700074100201440d00d10404900070800440d020100a000015510b4804000900079841c0c03904100003150103070413440384190003c0c0c41d580080354000c0307800d02500280115136034071522031a16042040c40c110015150319280c0074080200720032141d110780350040349c0c2c0c104000461500300d100012140707040c1a610141c0845408559507540d0181e034a8100145405a44280003a90301c4206854040c03182c2e40d2100d405038480301c407160860418001800c118483c0d400002a4041648104200740004071400c00d183c840c0d42c4c1c3d45245404d03091007002c1d6140c03010301e130412040d11075200561003102120150414040d103401c0d040110359400c1e950380781c0494041d0034dc9031034000894030000034100150507040e86040c82c8501081002c01403003964540e0031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 159452517 1250 159451267 159451289
    0x3050c0f09070c030203040305010507020a03230f03040f1a070f210509070e0a0c0306060e2110180302010c0206040b0103061109040c020601060210090b0a0b0607020d0b061306 77
    0x50b10041036581d11842101201540010b004c0000442d42c01c0c4101481400b0607000381c050380110f8500105102c5882031520240c1910740c0640d0380020210041c1c940740401c003101107580792a2420001448a55a100107043c0e84091824070044020403101c0c900490345916052600b6000764801c1d52580a01c40421101801440705d4501503009a0000d0782c01000c243c0a60784402e80b00c60300103400e450101c861a9410b038444000e1610180d151242c007008000500d00503021080c102c000600460305405c60b003c180b10414903240c4807150600c40455036691092082282d003800606c290084d0510480c2500554680300010b110280045242440b8580c00080211320382e0a5a07200f60007051520b1051aa03200c1c148242600c9407182c1c030a0000e1040c06400500240d031400320002d00d400d503907904070100a41494030301c40000d03407000031040c5c028a40d000e01060703041411003c110300e4001d4003800b07903210b00c2e240d40400502442c134008602442c0b0548440d180300400700320440c02e0711054412118060 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 159453767 1250 159452517 159452521
    0x20d080a181e0203070e0f0a02030106020c0d110303040609090b0315070c0606030c081507020f0c011d191701050f150102070801020a0504170a0203031e0408060f0103050c0f09 77
    0xc0c0c02212200c1221050010104a408058001c42d00d0320540d9000707036440d81084021310828030880c1401a508c20090310b415807440d0304102d402516210300b200c2031401851000c01c07140800c00351030744401c2e042c50060102c0380c0300da0361030a00926021140c403621111525000400001d820f000c58102603030001c1a10049558036042c4e003c480030141c0c03030703c140c500c0b035a02e14000c0300150792501031307400410110300141311064105004801405024001505540c8a050703916201500030521a8a04100342000002c0344020810140d41145005949a11519240c00b2040c064400c038110400d8420542c00ba00000754607668250032540141d4402c01d55800340d40014141d0540100b269110312810b2040c1c8645641e01d69505099800003071850021030b6003c00c050003011044170009032111a04d00c01031417010815004240c0703a10032900300b203410600c1d4403122101402c0d820101e034000e0181500f260700c2c5140510060008006c00e0004880501030f445d80c2180d40c4c5041140c02e044030a0041c40d1281c26 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 159455017 1250 159453767 159453773
    0x21f050705040b1804020a050306131a01051803060106030e0607020109031d0d0b0901052202060a03020f16030309021305040c050f0d06090c03021804080d0b06070b07020d080a18 78
    0x15821104d00304004003200c002d140c0840c2c0756030002e82500940c5031149520f030308101d801c20042e00c00381ca882c1c4212070724200c0020220046003810303140f110b07000e003042a651005941554100881c3c03080341ca816200b000000510350f81e0580c445081c0c01d41d040103480003529211001c03400d071440c82784e001c0c0010b0740303070076a00c0d84c0d0402011201c8007401c0000d055084a40d4603548d81c0f90302e040b0031035105015135903d50801c40d900c03607012048200107030790300c5109000c100300d540061600e0140204140401d980800c00420f0b208082048034400901c0701040b0041c8059460010050658480304034000c0900b08500020450340d4001c4c00d004036407242d900b030103160902c0144480310b800c0207115680250818071540c023051484c4108905180a4241d102d01c44d410f41c014800354a11641c000b4244030014010403000c2018481034070b101c44d42003480810410382c40c03c00601c00d0b0003001c10281011018800780240d80e600001c2071000007400391915001c554613001400e0880c0c0f0348207079400079800c00002284c00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 159456267 1250 159455017 159455039
    0x10f060207031509020d0606090c02070e0a050901090213060f140d121b0c030506010506120a0905031e03150109060c020906040212040c03061a0117090a080a021f05070504 75
    0x1043c021100000c0c43c0c503071600040d0340d4038040d0350141e9007241d480d0014003081030706d030041c220305d0100c0740000c05540c0d10f06031020f864000000c02242c551984c6201184600b002034101540e002e4005120310207103103500c0305c40c100401c8580f00345061003c50540004203000c0c100104085503d0050a90815a00702d03214128000c0c1c408030b0030030400041c40c41008155040501e01001c03140039481c0a07102c40d0840c5891413420806030000d0380b00e41400d01804202c910000711060b844604000003086444452a045142d402141c84900701980b509403414a4000e865019610403060034480350309a0009070019601054540542000907000d80000000350500c072600582205025000526060302c03c0c100030304803501590100d5100444142c10418000302c0c0c01044031170548801012078a444160000c0d0a00c04003582d8031940d0303002a000500303542e03002d10034034151540240e180c0e9600d0300109002901c804011404c40304040d401104502008858442c3c00e1180703000b074440d6850b040c100110111 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 159457517 1250 159456267 159456293
    0x406031a03070b09030f0106050a0b0d06090c0507021009060815010e040e0105070f0302030c0306010f0219050601051507050d18181a0301021305010509040b03071d010f06020703 78
    0x41800c040c01004401510100150402400392601c07107621030000b1001c05007001e540340a0180660304105050141e40d4a60340703407004641e00200415501c0d1001c9000201402007a0b0111544030701d42411080580d070014010901035100f25417901401451390b006039140c0001d4003648001644450000701182c000c510760120342c01c0d05051a05803140003000181c1980c00320b020000c4141d44810900881a41000700940c0c0c0c003010381801d50440c50580600002c2d40401440740f0704214456088080c49030080c0010860210300e500400d110b0060750a069a03207280038411680a170035500d0b10780003a880f070342050780c0a59522001601d602042c0150841c0c00c802c980c4a080c2c017449c2006400100e80190360480320490303210410115180c0c1c0340c1d0050001d89104003010314001e0740100100d400502c18090102c040d200c007424442e80701e40c0408c3c0450700500861042c07980500c00d020307000c0794580003000500e12559414410948680c0c0fa11a00800d0400c2032244002680c40a50140000707004542e44203 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 159458767 1250 159457517 159457541
    0x60516020402091809010905010501230112020904150315090308011406040e040b0f071e270b070210030c201c0c021801080a021c0b042001080c040603 66
    0x1a0742403103c4c40c88059020755030365066030f540d0440b04040020a0045500420083c14010f01345000301551401106441803240c0c1040340400790031520080d142d040d03d030750000161080107030011501c1003113444203042c0801e440341030308501c242c012941d140c0a103414460707055894020991a0a071499001480c400703640d5030000c010700000c10b6803511054107900c194060640400316051004200301903920140260f0304100302050305074440c1c0d10324940000e111130b69281220881403000c0d428034131701420010480c2500350701000003a074107542802501c10329008a030010850307080604c0681c01c484107014600e020031404480c1540b404e40107050400741d65290005e89089081011004c8124840d41c6070020100390420802c0066040c01582280f008001c01d00540c0194103000100f0760b5a000510000e2041c1e004c0d2404429170020007000e2202d15902c10321200e81400e0a2070168407440c0306900c0403030003e8031006120b66541c4200c05590281d603401c06218502818000300700c000d04111340e408 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 159460017 1250 159458767 159458779
    0x10905041d060705031005090601090303121d0a020415050d02120a0203030a0f0807020607080c07020406030b100611030f0406030b0f0a0e01170303010f060e1201060b0304060606051602040209 84
    0x2501e030002040c41040e01c03420560f56a1170341d900d0485207046c0659181d40255002d920804104642c1c0e0b600044d03101c2c1075a4042c1020802026043d907594003900e03813507045044000024800d0349116000245200310184200c0d404c0c014894525030003001c69103907100c0c0d41d501200028044001d07003445100b1400c1030929205031144001c458002c80e140d9403004504d1000503504804001a0543c0401d00942149840c03000d0411410540130044c80701802130941c408100700060716070215902c0e80d00c5035009590150711028646440b824156508a5a01c11400414500b9030407031481c030390210803030307805d2510002c40340c0c2002d00303244d01280142048040182c0103403080c4000b45140d61040c010074010b118000e540780c000c1d8101034a0840d4100c40310f000504662040c4014410a00254840400d4809130b1900c0c0d460745041c180001c054980341400f40c0b031594a86200445e00100160045108034040c10b4180701040e5541800c44280c8640200e540c0c00c150103124000061a00f5002000303048002080b0f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 159461267 1250 159460017 159460061
    0x604090b13050f10090b01021c05040905090c01030e030708070b040f06020304061d0316020609150d0506030c0d1109150a423209040608070501090504 66
    0x204089a4083e0340e03048015140e1810084d2005201040300084c0c41003e0040c8035042c580400031b540c2d80149140044179442e003019080c91644910255030003001804010b00680c1006400c031b50701d82418000c61400a0b0410b0340081410a0000840350041e5004d0020342c5052100d80f1520040700020707000700c0744051880141c001240f00da00185010314000c90002901301440640304200918540742d2060680061000c5103454440038124011710780c054078455642e207403110014400c0c801c40ba40615949002081d01042c0e0650750303100c940305200c1501258900449401007100d0100b001100818442c40840081d00d203041190800d03400850441d12469039207180380c006182084d858001000d5000119505000c2e031040287c10081000c0107503410f01c2c00d402c034000b200d80013540c1500800501410245070a02a511018881c2002d10000c0c0050725086840c1d02c04985c075446a4901032056081030008500d18801090100480e5416102c40d4000380c070300003d00c40a071101244072180035800003c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 159462517 1250 159461267 159461299
    0x210c02070b0d0b010306050f030706051c0501080a0302190803010506070303290a170a02010c1401061404050a270503090907080105090a0902060a031d0f030301060f020c0604090b 78
    0x18040e070340380c01140810740c90f84520005049a500e80d108912542800c6008c0c03056481c08151041554038914101d81d0f40c0098090010900040c0304280350241d241400000d005103000c1102c441c403d10a500f40d038010310641d440c1701002c2410100240c40f003002007004100502e0301d04001c20006200c1e080101d85009443c500003c49958608441307402180603807008403a01d80210343d44040e1100902600c490740f250038696a984420070002418406001180307803d02284180813680348000c80001e0008949500042041180035040e040c01182010042504019580074140c4049c42041d65071140350310700000c5800ca256400d5080d509c9000801020b074264440b2820f281c03056001d910b9040346035140c2024000590170040c0044241440c0000c0440140e80d4981182c00f8500c42d80380105a50085400002112100e4a0204d070980b05e000c015024940000c809907042300c4e519164140c03101b40c4c1310700c2030340c40d01030321031089520002c100000d001030f0030294031010350386030701521404110301500 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 159463767 1250 159462517 159462539
    0x609090a060501140109081f15030503040f06030e0102033c0a020301030c0f1508061518030705150403080d060b0a02011413030815060d0c08040b07210c0207 69
    0xe04614514502005248405d5810082010040c80341000610600d0705a000400844902a041441c80390b1181c480d071032040b030704c0954a40175617040b03400e50b55100c1c1e40f42c0f0311a220343d2061003a800468100814201848018401d032403007041d0200c030184a03032560f4210030842d800e51841c012a0b02c008151442044101181401d1182210150041e075135415420501203104642d409401c1c42c880d8920f091120349a10010f442d450117207420a40c051391280400225215400d8000204003200446cac03040704012107490403c4a0319064044d00c0309075864070140326030040300c8000200c444008100c1000019080001861380195654001510035210020120294008203401e80103170345031a09010308a9280a00035000303418100c0002100700c0c165009081e011006020711030150310301c0c200082d1500ca5108840d0a0f00310600100100003111502410400f01580d0076190b401400f030009110f20f009400e030b42143c5403180000d00805040c0d0f0b280f80d003d800120132000c1140240c000000300c10a0346 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 159465017 1250 159463767 159463769
    0xf0408010515040c05161718090c04050a0605030606070c030c180612020d02150a03020c0114040f08030a09050703030306090e07180f06170c180702060609090a060501 73
    0x22800480d440c1403801820a4010308030070000c0c840c41c900030034905007a070400f003200d404041e518031a0800c24800c0c00c10f010840c603c802e400c4204070380018a0f000c952012000303e40c40740012601a080c035182c03034068421902030b60065a4004014210078090640110b005d198400c8000b02490310f0100e1980e01c1032442c2d500c0b940222180e5513504020701c44041c141180c1d400b20418280c0c200801890f10030b001280c0030081d000640074228260284040d0346680e44000d1922480c0c1c0038070760340c1e410710441c024025400301d000000694a0008003030581020050f800d0f00558100c11a03104442251f103a000c110391002e08404501035558084034005407060028000450113514001031562811441c041030b68a01551821160842e44091146000300d62040700e100902c1d0344005011442c4000480c010100ca8012100320541220f410640620029021508c80c00c181d811109161101d08280a801c3c025902640580c11180008400303003481040b4941c000038403000c65007901e07d5134490408a40b42 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 159466267 1250 159465017 159465029
    0xb0f06090f0a150f0c0f0b041a0f0105030c01091401030b18040305120919030807020c060d091e03050d02181309111507060209030a0c090f06060c12030509030f04 71
    0x604030640c3c881c0e42100310014484440d0074914100320595980c1e412050712904000c003120207032000301301806100446d140c074425819610b60349504150a00500102c800d00c1600d11070b10980702452215407141d100101221a805262803405074100300650141a40d909829081181031692061003e840c00e83c1c42d02490007030b1a00c9540324440c5410700d00c1c00e80014403e64142d03100003405140d48071301082103003840d0740501e4124003d4640c45400ca0801c110080c125501a101045c0360354486020f038001c030005c62044100c804124001007900c044903042c0308000d004a40140400398401203242c00070803481c1104a40c0c082e00f41500d00008841d84540f400d03800c280350b500d580e608100800f10024400143c41110720040c02040d40d54184694822600020041074000c95000310a8404009103040258061242c640b80e80d283c02c1344000400f840519400424100000010b00e203000700099504203400c8910b6100da100400c038250064800940910b005101c00c01c0f00440150061020340082c02c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 159467517 1250 159466267 159466289
    0x240109020d0e0a08040f0b03090c010c08040801140a05010905090307080c10020d020c0f03040b0a110c090c1804090804060f14040b0a0816080f040302030715050106030e010b0f06090f0a 81
    0x801d015264000c0e506e6500161000103041041c4006010006030b0503034a02070034039200701005458603040480d40103540c0030003407075800d10b40180d07143c1b8040308404d8417941e080502000503070307642c110640c10b841c400d49a0000303542041007038002048201c03008000c4410403c0c1100e032940c0300058031408903403141e00e100d140a90f01090340d0b882454140036844104401c10b0043d801e1030b08000e8403000c540b00700326a40080c0301450b000400c00081c28130010614502c02002c612407840c4c01d14243c12641e1150b50908043c502c0e4890b60310207441d19100340092160040f800070f0416081c4101030380c007007840161103014450301d040041030107089040140b0161107135802c410744030f42042201421650001d010811400100d100c0020301641c00118075900103000301c03400b00716866900f401c0c0c2c01d5201d150301c00307482c0bc0c0040b080d010001c9450b0700014121000780d0b8040014079440d11500d030032a0340f51250780341d000011b10713941c030120b1620704003a19500d103000700000c02c00030601001481d00300d803641c01028414 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 159468767 1250 159467517 159467519
    0x19260a08090f0109051209040e010c0e12010c0207090903110105010b0d0605061602150d0e0129010f0e011b0b0403020105010e01240c0f14240109020d0e0a0804 70
    0x41c800340700c40030444180200030301880110b607075826100c450300d843c440428880401c1e100605d130f455800a0014803804c1000700010081200010807050030502a00d000b500c842c107420808600500c2094a41400c07035001c0c0840c507040000d03980c06807007100003e4040164920b041e440000003071103103500826031080581d0707890405041d140180c80d01c5512061013007205108880c2c42d07420070300f0140400c03541103901403540c4c84200300045081c0140b0101923a45880c0c4080c1d2401200158400000b62000c1c200101d03200d401307444000203c1320741382c8040b40001c291b1700c0101c82c59801603040304198501410a43d0007503081d003002003007141442c03505035005c2c0010414001456028442c1c0d6015125034241ca00d020b6040011100b100041c0150b1142c0c0c0745544084141e4180c45640c1507545164071602e0003243c10160b0400d0f002d080b1912494043c40d0195210780390f0007071030360343d080102c01c0d44490710740102da0329104480009411207228845050344901e0140040030060081240a41c42030380c81c15255 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 159470017 1250 159468767 159468781
    0x140f0708070801020a05040504110705030d06050312040b07020405061216030605010b030103030c030c06270501061e0e0405070b130806131a190c020f06060319260a08 73
    0x100340964080e6000f41d1040001d01c80c900e510404503400c0e5142030ba070204a900c89240a400c2501c03a41c80060928080071a4102074200580c020001320745044040312990205081020307283c0c4140e209402d00c030b40c0208a4800141401d8202c903900c200000e00c104002284d0721842400d08402c00301100203c2d9000d9000c1c010400d80c1e00c03030706025012a0790311a00b90740c11a64050229413822401400380442c000d4000d040040c140c008030300c4140f001c80008507016040d455a0108420144110340359401c005011901d95180c0000b4440c0328a0000c0c2c445501d46481184ce42c03084020b0802d030b4440c0940100840c0d0f03000d440008080c0941d010800b008414a003408107414604050400c1c05070b80c44040c00c0c1e101017078109940070703501040012903014545031983e0007858000e2a0030030011a6081012040c1e0554011401e032a444c0b042a06440440c1d46100400d0380710108100000203410401c01c2a401162115290040805c0e440000700310100204155086541010b04242d00240d104000c206503 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 159471267 1250 159470017 159470023
    0x901110601050a0605070503040902040b12091b060702010e0607050d0906050306031b04090203010615032304110d0602120709050d0507090e01020409050c09011e051204140f0708 78
    0x1100104002400d01541000c0001d142601144901d80400102040361000e1090920480d001002e00740821542d4035501e81007054103400c011410070703414881c840020480000030800c000d50000340c12038058160482010442c581c0c0040000303904103d074402a9034a692918401048041d020b00e00400d07081c440c1c198000c200151070341041040100910510010703031000100c101003503030454035040f000f240c58400318008210319003010b98907600380301c0005180180555144443c1a056400780f100703c088900017111182c104801d9112a848000002c0100e80c00041d803810100000706501104281030f21420181d270441a4048a800c0c445014000107036042035202c0014102643c00003c2c2d40420f84900303403280881c1c0304000e5111384074140034050883c00c4d81154080c10503880200094100030044240782e4118541c0306020828814107503140e000448100f035030001c066641e0300e261051030070801c00c03000005002100e070307204101c0300500d081c2b50074040131100400c0503004007419031502d818107107 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 159472517 1250 159471267 159471287
    0x9030a0905011b0b0117010e071a07170703090806060102030408070924090204141509010809100906061a070c12060207060905030306030d0801080c06031b0c1e1515040e10020901 78
    0x2342030b0b11840e401c104007000034044400c02491050280e40719003050420b1a84040209004000c0b00b000080403010943c104c0700780801d4902c0141218001d035220070059039a4403843c01011170551103800304000c0c031882034011943c2000824080c46000800510380c1c20342c20040c0d0800e007002600440c050000319100c0d0705030040004122070f0b201c40800000c0e40403446105504075141040f0300302c0005084040100585042d03c2c50b980c034108429660b5060100040c94140900741c01ca8100c1c281c030f510351894034402e1341c4030140c0103c100d40340185026200c0048802d905030031241150207020075004504a0b225801c081c0d0300407005955640744c03074020142404030b681d00400900c510040140300e080000248610751180544513140e680c0c950784007a42c00d0303000c2400300701c000c0b1800007214420300b4400705035820f180c2080702c29600c0030031015072241e031200c071070b80d180003590544100002d03000035800315100002038000e03100103003414040410314200f01c811244442e0107500081e191140d941d0052541d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 159473767 1250 159472517 159472541
    0x50d02010b0415120201030e101d030717160f0312050a0608030a1d1201060302010219210c0c1412061312051306020606040509030a0905011b0b011701 66
    0x2d821290b01c03c3c2c601c00b12140903580003004100200c00440e4084c1d442001d880066008a5007045a924058000b40c40da03d5021803032088196891080b4080000550380c0070b59100300860080c0c40008100c194a030001e0848071400340907000c894002c0788070110101d020078000d554482000c807001034158291940601040c012501d0b00703000700468800442520f280100c03d140089240c0b20f91004103200c50390307100d105a0b10203400c115120801c0790541c081c208580c801e800b9101050310002404484d054001e0025210500d18144503d44024411504402d01030f0303030402003451350503515080b221040540003142d000182016030b28251805503c4200c107000304000070f10907450485201380f221240e107240241148030f549858110240114140c031108880540d038003805075501e00300207542c1c2000742c8900f80aa803404000c00d05815000c022920700d14100e4030b071285180d2a20004650910743c1900b0a00300491003079a8030009420a0f1603640203040300312480038102c1651800c2800c41e010000c9203 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 159475017 1250 159473767 159473771
    0x2150c0304170a182c250504080102030711070f06050708030402060c19030e010504080606010e010915030207060e0a02090a1104050409050102030709051207030b090f0307050d02010b04 81
    0x40040c0c003400b07022002d0248984110b0315200c009100b82d43c055000303540c1e120851611840840c0c107011141d0100001018517550f45130051041030410304100c030555012803200e07180c55250000e410301030450055038480346402480c007541e5203800750072a08140c5003080013480f551441c0f0440380d0101305082c0030308804180040700380d181c80b101130094800d105c00180341000100000b001d541e1081c064503090218a13040d2134824400d1602c86406080b0004d040380031034511901c07e91075501c140203550642e800b2070018482c6484800042d41e40a43c059a01c50400070741c054007182161094144001c841000c3d02e02684400d080d1912009a5103007240040b1240d100307040325000740e40c40124080d08400344c0100000c810070b42181d44030661240360019a080780c100700c1c40008200381580158850507503541e4100c01c0c070b0740301c508001c5450000120f0680e50750200344144041000d41c0040c0c1d41140800044070350400c4c0d4251140d055030820303c801c0e40e15803c402828140641c085c0503101c0d15410885007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 159476267 1250 159475017 159475021
    0x7150b1002030a110709060f1815180f0f06030b01090c05090108070207030506010f0e0f06030318040b0301060b04051806010c060b01030e0a21050c0a031107030f0302150c03 76
    0x1d682e409204894010403c61501c4080713000c0c014030002000e09a60081403203440d440b6071742d0102d440c9142c1f144840d058920b03240c41204901900c0f80007044c0c0440f44a44403011310300000382e08041c1450484080e1180c0e0340c10205d00300c071010f214648001c0e45440d00810101d03d1818002e90801e4140d0080c0c1c01c3c94280f40c0d081951a80c441c04030b5000031001d080c41e050316250444128948030705074000a1440c440c020006c64900c0c01c2150b0b6104480003c3e5003100a81c0d2445050304882c0420744103143c040c1d10920140503008100024565090400f60000406000c00000a820354090360f21000340303100e00103420702990404440c90242d507030107044004100d0038904c0008100380c80c2640041c0c42e4030354032074500d50160300ca500450399110a44e0100d540c043c0803801e201c600c00660104250f03042224030010f8800303d000f082907607580d00406020301010100b0b5202501c6210041002ca5014010b518000c800100071481007502da82c0203a004100d007440114290702001d0010b0b220251000d02842 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 159477517 1250 159476267 159476299
    0x90b090603031209070803040f0f0503030c0607050306010509030709051509070e0f0a030b0f150a120b04050115170606011d011d040914010f05010609090e0307020607150b 75
    0x1c00c490000c11070340b00d10380c03d5076a004807003410191680c1000125010014000841b0804082c4003015102280c0c203003c082562241003684e00c1c411042081da00d5046100050a00d60140d03010359030000040c104182380990010000341801c98035001406041e81c2e460034490f05044062820f402c401c4240c40c490300342c1c189184080d081d100e403820003c6c070512515500000903101c980d9201d000b50344c8402041001d0070000030030b61003040116507001c48821050140c445030310300220300100f120350340c915605096a540e03d5a500c920320052080d035256495042180100c0d1050100a005003070350242d6070545000203900c1420000090040d90402950300111321407204100707a90f048001007400c1010022412541c0680885000c1030301d140d026140210103014000d0081c071a501c00d0025074001c0161034482082402150402e0041100007900094144000011507104d003402d8401e10307007228241407060b40007075500e41c0804000c079607440b1002c0f6440d15024140c01200549681164540c030301d181550 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 159478767 1250 159477517 159477523
    0xc11030708030a090b01060f0212031e1f03080714030a1b0303060e010b070c0e1302150d0203010906140405040213021305060a030905070801060f0302010311120f01090b090603 77
    0x85001d8110304000003c9904800103a00040e003542e03102c501c0000a6a607003001030804401204040058041d00226004d1800340600b101d200d2103440d1107409001c070256404a1b50101c005044048070050500c03140030a0940312070030001107120301c0c0480c0d981c5030245400c0b480748140a00300b80d010380c42031054503981c1e90090312401054081409500c0110300e44c4c00c08501500030b60f4003408500e0840800422000071140040c6082806176015000359584e502e8800803400b41281c5402008440c040b4107001458901340d5021222600e5103c0740c100410000b1540490b0302c01e0340a0040ea5030384a0040104403031100205460800072039042119141c247c010410314003990b80f103200c01c03e85c00a5001c0c554862a004c1c03001920340500070b240c6a04500c0300150082c8440e01d400c2c1e8040c460224006440300c0140501c0040d90403012081c00142d18560040d03000c0c2c11a107aa1200c0caa1090029240b1488200c1d0880c3c0b0071541104811070715498640e0403411240d080b1041800383d6281402c00c1003a403800 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 159480017 1250 159478767 159478777
    0x2104050d08030604090f120212040e040807030917060103030e030f0c06130b04080c0102010605030a0f030f0504150315060905090c03070207150905090c0702010807110c04020708030a0c1103 83
    0x12011903500e5a070f400000e40280400c590040400c030f11510f0140500070341152030000e2803402c5e02180c80c90602c2000f0005580154414800031105890024000036542c00151811710700c203050804469403115081d0f010f0449500c1c495440c0d902160041003899480109031580b031009034050102c001c080d0b00d80719290000740111500036040050f102c00a400d400e903844008040d15a00281c640d9181d0014503166a000d8020500560a0520106480c0341c0407a000c2981a4007418210160346136913025180310b4401da100785c0c1400700c18000040c00e2a000800642c600c9026500000c5009103c0060038040e040d03604400100402100c0901c1651112001c131504002d00b405035603260717a1150000ca2070840c1c0d640144402c0510035081c404100e411040803c155101161b07041c1080d910518100828040c0d0440a8009000c54002c1000380d4051f00a184040d06071900307503940109143d001c10140d034882c0c2821101c5220000400003032402c0ca1013a841c0700b48181c68070040600e00111007503924010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 159481267 1250 159480017 159480023
    0x302030f0a0b0102070b0d0204032d030809010f0518010e0d050f09040b0319050105010909151d030a120e0705030706120b0415140d0b0703180606082104050d 69
    0x1446070b4a0401d030780200000c03001400340300e80c031035615108440500e0194001d4482103d1820502c1104207854803064441d03548070b8400000410040605d40b801c454a840c05440c800c465541c60488894008050055a02c2035105000d844c0140350491401c50850300700306807122840d000000039001d450740c804122100010200179881d215270102c400200181010500181e05104600f04610b184503e4045514a203000d00020009a0b07a10b251880981e5030101c4014191703200100d068107191000d5001360080203001d4030101c4001d507a2600c991540d8007280703040000c1802203640540c0310800c1d00402404d50a448050600341d464034001c684c0e1140700d801000c0611400d442d04404140f800c2d40014a82940100107101010110544409140060251030310071180040b04070f0482c100344003218842039200aa60525075624141100205907a03002c182e481070340c4500880101d0998061312000c3c20a1102030a264264002c8041c80c0e0f5450202c41c02000d42c00b80010005030762000c0d410f054030380d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 159482517 1250 159481267 159481271
    0xd1416080c0c12030f01150f1b140106090509160f260303040303020a1d01080f090309030f07060f08090d2114010915030b0105060a140a08090d0302030f0a 68
    0xd0300b4054104020050010030014001c010000d50017000440c05040360841d0310450310076a144041111440e581c3c070074401c041044150840c1100da00d02d204400060b0041d521414002d03501014907007510400d92200c40100d48032424410241e200b400301c8440d0510030b44090390010b00d0040284820360441c4941d4009003114030b4141003c120006110980520802c1942d03501d2615103000350081d009000c0410020b803520040d007540007118a050000400143c4848646030754030180600803d00040403070201d40406c3c0188200d507100dc22152142000d03040190030b60703134144000280301104c9102c0c10010059501c05110b440340003c41d103409a10407070b2600c0c40b1081000c4c003280400c43c440c0020100b145242214900300b6004207280c841c1a00c200b00c0080c000b03400034a480c4840d420040c00050004102d500c01080585006402045011214207003074800d1070080c034800c8680e400140c1d02c03001080701d00741000030585081c002e190903030b10a81001c6086040c1213080b10555000100245180d907 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 159483767 1250 159482517 159482527
    0x1051912020d0f05070308030f0f064b0f0a061202130f03080a0f020607050d09020a03020904050d0206061827030a05040f050409080715020f0d1416080c 67
    0x46071650f841141030b04081220350480c3ea030314081440c1d0340200c4020180c441c601010814903142c4051050051200806800c11000800b4441c1c402044409421440441c03003613215048062001c0e01400d40c1009000c000b003240301075428041d0700008841c40c14451b064203a02403014a801105061007860381002c0141c440710b0046140040030115040001c03400c0b800140041002140c40c02840c0956113941d405140349040c01c2c0c140da4525059912401256003030021146415090748051042400104691030140c1d0341c0c2c022070303c2e00000703032419202034018200509869030100031882e00510107480301c040000c1403046900c0514405030011030018130040f80000c04000344071044020112503016203968440d504000740c07044e8018072a12201e01001c07a40007503c1d05c0c0c14410b14aa290b00a5407580c601083c90703684000301c0c0303064280c07a0304541c0c4c00d00001c03100141000c0940003945c6011000507140706001219941c20380700900390204484030449800e0119400200f660b0414900d074029900d0b0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 159485017 1250 159483767 159483773
    0x606010f110106051f030b030d050306120705060c01020714030301050a030204020a05270301110c0a110a030503071b0506130e061210050105120d0e01050901031107030801051912020d 80
    0x507101544c41194040003c00300e034000150000038040400c480c5840c1080411803d9051546a881a20401d030201d0014000188941030400080190000c1c880c2510800d03070b103a4000030348581014498141c01d070341c00321f5403008205080314035480010700a40118110341c0741200141c0390a0f00750000a000304d8000c910500d4013030085054840b10b0242103401020010100c907056031802c804101070f442903080828052941a40c0702c100c91400b240d8a000e0040342c6016220f214000c011f4000040d04112001c5000010071000d001811809200383c101d2810000001c0303240051007003e4028078402c180411070901c001482c454641d04440000088415540e100300016604170700d00d451500c010301542c004044050136507401141a580100e60380700c0c1080d0350000301c0780d40b6031031000d160020130b04051a141140d8020b1000c0c01c0344810516004ca80081c00904110540e00150401c4010030100e20043c03207680341582c140c440d152a88031a42c1d040910341807000d0444040408007078001d81141000c1e4080c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 159486267 1250 159485017 159485021
    0x80a182403020c1504060f020403031704050f070b0301060206181e01060909151107050601120f06091b1a0a0c06090b07080108010506060301150503090a1b090b030606010f1101 77
    0x94020b083c0240c50161001d0007080c01c100320104c600320703000e901e800803d980601141c4203440540340c060352180d40d8807019008090801e000030f403041e43c05100d40c0c0c01442c10280b0410999002c1d0030954002d80e200d5140400c06840d102002d0b101c8824803000b0503d948106000055040389041c8001e0404049201c000585d801040c294201800881c14103900609128490765090340d0200a414100b080d0b22400040c82e92601030444004c01d03580010380100b1015021224900209000d071201100c50051030380c4500884409410880c1c8a2030a01ca0394072000e190700302400010046c083d0109207840200d00b4050f42c0388140703c025003d108090401405000381da9001d10115907002a4034201414040790180800000740f240d81030a42c2003400003141c03800c056040c0c0741282d01e80e00c01402903080d2600c098900ea00300910050f01c80c404c0c0c000120200d0503000d400003007517401d4030703a0300c41560415000f441130f0703030410b003410b40a6400002449400e981c0100c0c107415400881c83c04d001d824140490070b0340 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 159487517 1250 159486267 159486277
    0x1030f02130b040c050c150708010b2b0c03050f0c04091107060f0501050a0f08100b01021c0815060c06071407080409060e090f0a02060c1603080a18240302 68
    0x10700989440c250135500e503002402132400700c0c0c84d60b04886585c440080540e800e01c00403075040d00090600c100400c40b204112002d40041028100b0a854080a51076499000b0000e150091845030b140d502c0c4034803060f094420349801c043c0c0d48502100500e070442c0142051320440c0310708030310b00d41e0310405800d05d604940b040c0e6401380c0e0301000501528440b0610312000e01800e0040c14403810489000042c8132100704101011540d40f00301910b80c81e1852008080180702e0040141d05600401c200c50000300561002c2c2740c000c0a2980301d4403000d0615201d0300002d642092440d602900003040000c01c0b0160005410768454194588250f039034102e802d00c24810300580d40024217541022074041000b0a441e000308065a910350381407092580c8124000d0307550842c50700b00300419005442e1140140c205000241141c0341c1d0503080320039829074500c0d01c4841810790351003680e04050104d8400c60240d40174030040188040c40300040c440909054076500125a00305088050030410112181e42da406601511 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 159488767 1250 159487517 159487519
    0x30203060f0a060503060112031b0b1315090203061b04030516230f040b040e0f011b02010b09010b1e030f04030f11070e09070b0406050d0e010501030f02130b 69
    0x9a85418212410322141d0400c0d105400e10038140310003c5001e040006e0418102c40d00c6a0320010300e541292801e845075000c0c0c1560290907551907880310045040058454080c18000d9500c0740410580d04007050210550344041c080142005410340159034001609508003114a50b14441c42342240c9848003184900d600042680c060514000c0402d2140d4264034121740d140740c54500c000d020f015014030942440d240c0a54060300d000720000700d5041c02c0d4084844904083d2000582c0420010703454502040f003110109280c2d101c8458140002030001d03074100d40783d0180024450042041d00240d5050014052030380340c00404600d4440c0c41c0d030181c51030035031801101c0280b80d032800c4c600f01000c0904812141500420700401031140303481e2081462038150303200c080c050700d412400c2c40d4900b040c0d02d0000e86104110300c41e042c00480c07102c400400500061200351107603941c6800003681141034610300855080c59034500801007002c0b40144440c4c440441d4121405855114208034040003090120000d03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 159490017 1250 159488767 159488773
    0x30609050a030815010503010303110703020618240913110a080f1303021e0705090f1801020310090921021f06080d260f010510031404021009030203 65
    0x90061040204503004007600070794400d40c0ea5942c640754022400c45500625000484c1000100080b07480780010382082e009000684548680d00e4000031801e4001110a80c0ca00000b210410140c0c07405a81190101b04844419140d03030b940c0b0449903056001d04480c003400707041560340011040c1820b900195051452014140d00c81400075002844088215070007a090031440c070100e4000c03161400880603659044c1e0040c540b90703000c50002c0c0d0650380b40050b440e100c1c1c4030f40e80020640f5a256100603116007500b4080d80c220f0315044050200c5060251f884030126441003003840071200c0ea6076800810344800c00000714400d210351810500c0309107401002c0310b542030742c182400c004682c00b2070b002400f0504000250300d81804107084404075003482c400d040300b592022040c2d019150080701c41d164101d140040d240001407c4d5602603422040485008584555010040c0b285203010541d204500c0047c0c5004c0200701c0d41144015804500580043e106086907410070344403922070f045071005940c0c0903050b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 159491267 1250 159490017 159490031
    0x70e01022815060909030e01050325020f030f0306030613150b060c0307030207090506042304020d05030409090c0603050403020604020f0613091b0f02060f0c09091303020609030f09060309070306 85
    0x70400030201c40c0c0045000903155060447c9035881481a68001c058080014001030580d040503046014041c04050540c043c0c2c0d00d5801001030140040d004113074150381050340d68074285080508019004240480410703001d440c0d10082841040805201d2100c180005a19410140020400d004145140e5220321001545900b0190f010608500711502c03140203000303680b5018100310548411079000100180c0205a00d810740d80c2086043e6003183c0081c01c00c40d8600395586481c0d085500c540c108582d429200c220210400c102000e5207002060705150070862418586d400a40361f58000e070010b4801c0b109140000426a140350803915082c00303403400400d0701695032920307038080d03d2160303050b0710a10420241100c42c180140d92410b0350402942c060401e59842075201505410007401e203003036102c028070609900762107046070390380500015001d640140b112450020f14001c00140203804940007400005c400c2c501c1075007981d007402000c03101c1d140c89540e142021840d01d219a40302a20440c2007540e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 159492517 1250 159491267 159491279
    0x207021c0302060c09240903070e070809070b1815031f0504020a08060d0c0e070c060f0e0d030216050712021002030406080f2706070e0102281506 64
    0x100004180700b9001d0360455614480000454099110701541242d40b0044001c0141034009840c5412222918254240300d004d0011a1a00d540354000e0140c01d01044e0600c03030343d40e81100d0f0b00f03236000d808000200921401c0028014240c01009c0d0028402c1c082c50785c22a90540d01c00ca40f82c90003098911096880345000c100c030700583d0030060b000300040c42e0107110203d10350030240221130074182070b9121908551204800d020f070710170100740d00740d0744a02c166002240c5403d00c4078007540141800c1d030f02c4119045480c148142141c01001c5011041450001c6c10122a000802e84003440c0701a03040050b10380d01a000d01c944107081c100d000805c075005548000c120383c0b0604031400d281a009840f80341145940c000140d9583c07207540114408540907100103803c5000c48051140d11407403009200c124554103024070200580c60b409114038a030440750810202c594001120401440b00b48000c01e1050603882c01c0e440ca2000d1541100f46040f031140d40142802400003c12440340d484032802c01030695514 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 159493767 1250 159492517 159492559
    0x100305091905070501090609030f020907050d0e010b0915090c03100f1e050114030103260c060a050a0c350903180126040611070f0210020708030d0f020702 68
    0x805205c2c0802d00030000820803e1040d140304003981e61244c0300e8401540e40c0d401f081200c0307500600c14001c0003820808508400d40500401e110145580000703c1c0002d5124200010107a008090640c0c254105842e0240c80d6116564546c008250070481941ca0302d400309280d4124195802c1110400c000c101c0c006030f0b8120b050b64420411400d580094060b81e194001143c00c051a1994044603260501c01031000c82c00e940c5148580c034040f10441c0700b0b201400c80304d10644c0d4012044003421a000003080100c1c601650180700c0e80446480c0b410880a41e0242000e02500745a124808144031400c981480241b80169249040040e404080e040c510b080940b4a0396540301d0208082401c042424488044d4001e0788600c801542401c2c2c1001801c5500c2c441492800c0c0052044d04d16540303405401245500d0100140400c600030020903508281500501a41394a00c101d00c0c01194017024040008810100c10790300d507054020300210744444880c2851002c0e029444019500003620042d81255460130 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 159495017 1250 159493767 159493769
    0x9182505090a0c05030106030e011407030504150209010210050c0d0e030c07080c011d010e09150a150503070809070302031c110d0e040c0215040507030b0a090210030509190507 77
    0x100d441002580d00d0501c2070003a1100402c0d00008140240010701c40c807030094010300d0380442700d400001307020b050184503285601010394480c40440d51b00d40500c814000841a104851529400290b29200301c950000b96034800d0806128041036484010417280c264030320441d20340781c40007003051000612000c222500c95100710782154851003800f82c001b40140010542c1c121241058540558140c110000b50303078120700c181046410005482600301c040e960340007540380500759400f4000c294036100414000c1880300c2d03403c200700101641100c0344076280d0000840e54070155519103036101e43c68400b222441d04017580c00080d07144c0115050318075481c0791020404c0c0c0f02c1844d540c4d0fa54450100502807034841203015400f00000b0348001014072141041d420201821a503441155056001c00030f040500905c183d50440d902d0b00f040004000b40083c145e0040d80050840c2c004129000c241d500107480c2180c5001194141350700e510010b50200b82c00d002e290040080e50700d00b80c688902a1810742e40f10700031 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 159496267 1250 159495017 159495019
    0x50d0303110f28020d0503180d0801180b13180f0812070e0d06020c1e0a030e03061005040b0a03020409110301180222020f040b040501021b09182505 65
    0x180460f00c52806141e079407003502a01650003800b540c5000074012111584000c2030850030a0003804c0001d4609000c012068002080713654045031941000e02c80c511501004030400042d0b0f080040c80d4000c0c0c0e494004142c0c1003802c494001a424045905d020348002003810701420101c25401c0060503c0601402008079007000c0003030750030320780e25018107890711002d1110245d000b01180f14000c000400a6005007000130741fa00450312844000b0b0442c8002107403491100f04e00390000c9640c13500305034200c210121080000c41c050041ea281400b6000003603802c0d0711407036214a4440302015500e8807002500c8002d1030700a0014820504c190824842c0c1084601c80b0a000e0342c41e1016401c2c042c0c10445100110650061003820b0b00d050180702c0f860300c004101800424240d0800c03024241c0981c1d640100020000610b0545d03d6034a0314001900f09491011011301c44288182201a5940d503030640d03641c058030108001ca0701070088800d880c64005003400c2c0400080b409080340550f1080c1700070540464070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 159497517 1250 159496267 159496297
    0x309030509092d06241608131202100912080a120501060c0b0a0b010e04020915070c180504080a0f0c0206030a0e0601152a0602030a05070201050916050d0303110f 71
    0x1c2620a552402d80c0b105e002c04031458020310110a2081049405d900c40c44d00881c1c44038104020410b8007050030b07039140e010418400001103420700314140003125600c580607509100726541e261201c140560a50b1035130041c0103030b0000a00000850007421200c8010702090b004104541c2c560102802c017401e154000d5514920034000220002c1c501c0c0907034000b84034103030b541152819a80e0140f00194100482c45030340324044100c1401c4c0c07200f104024184950103800104003461604805a000c500901110030701281007104100100b440c0200721040c0d4040d40c0741c203807002ca04140040713401c0d0216620081d030102e00002403015051068100760010609081503580d030f039a94036136580080b09800d0012010402034011145e048150840000507110703251601652225683e0700c0004a85c0101ca0a402c0346540c2c10501c18460350910501d82e101030058024103041e03003c2901c03000080c01910a9074851999031920b00c0c20940f003900450380c903104020007140c07102e20081200c2c0071074201d80010030340b00d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 159498767 1250 159497517 159497539
    0xf02040b040512010c0f1416061b080402030607140c16090e07210206041505130e0402090a020a0e0409050601030201021203160e0f0d030c030f0309030509092d06 71
    0x7418800c10381042695210184011b030703124001da9090543c8911906480740900c5810848409401c00304102c900c51040040c03c80041041480c12030303029100e0340c0800184000f004010b031000a40c0c42d402c200c0600f0314007000c40007a194107020384079552901c04540103c0305d4003240d9000b40d00783e080030703140440d00c00d00040111580e050340d600701c40e00c04e00070a0401020305680c6900344d60418041540050501854541c07110301c1415404007034030055000960001e002600c00d01fa08058001a1156032400552400c00f500099004400a0b000c0d02c0c3c1b0b20350002e007101c002c0340500c03a090200b0b50050b200707000009030781c140540c81d03140900c801e030301500505045401c440c0c0000c1c12a403240c110407000c3c1040b480200011141c40e030207000d0968003c107001c0b0b00c040c059901c040000b060180300383e81d40380c00c014161034020104102c41d505007051506100c61000041d8000c025680d8041054800000380d0790340f0740f0781042c0c0c94503a0030b0100c8030650044c1c501c4590301151078070134810941610308031010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 159500017 1250 159498767 159498799
    0x711031b0406150e060901110a0f020406050607050319030617061501030b011409041118040606020f2104091113120c0303030513080a0302040503010e030301051f030f02040b0405 78
    0x180b41102400007030310403009858149410070141849007018907141c188e0700000c0d01c01a240a81c04030741550383c0c1e2480d500341021442e1a005420107480240c81031805c011181c3e48070f40c1e0742d000700f04090001c0135905001000e4148a0307801200204012500c550101000805807138580c501642c8941900c03803003019088282d40a0f0241068805060b56003031540d666054002e0380541090340260b5215403a074441201c2140c9200181940e0900b4000481c3e001c0345003003c2000b01d601c0d9a001d4025500002e0395450380d4a000300f0141c114146c070741c0390074401031141d1000c15103a1007540c1000041c01e24101140704000348100141c0100b001447c94111400e4a5800b443c4403203608000090440801020600c006071203500038540059484003000c610081507070f00c0d1003054014003d4800000c0c2d000c11f04000c940f9007402205850000702000d5071555042c1000b0a122110300c0c40306441a14070003400321000c611076405102d109075002070441d02c8940754001846164070074864076119080a00082c1c1c44 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 159501267 1250 159500017 159500039
    0xa02010510030b010b0304151a03011503081c02070f120809030c070614130b0c1509030711120d03090b060603070207060e0103020705010221090607140711031b0406 72
    0x19240c00111020041e071901420320341700d61005104560641030b03416602d0000342c00c5d000360b446140581c03119101d424800f00c213040c216402d52120620420b0101420008160700100301c07040d46c03e08001064010741403003860806407048000091915a06020700c8050120000c0c51600d880700c903690790211030700c0d2500b4581ea68020883c06a0107900000303410007005018003040105004580001030401c04024150346000700b0070340c08001840800100030b034019000b4010720951900b80808226035041550200340e89029008004142c0b028403c0e0380521540c61201c2d468020401c034040f50080c9180c4100100078080382682101c8600098001c91020318190090364468280c580c010711456180040c21200c0e10341c0c0018050606a00f0408040820003c2c0001d1280c44030344084000795241042c1c060495010041207101e2940119042c0b20781d0580c0000b01a1001030300320403060f142e69460178000981c0702c2180130740764140b040c03428039801c1c2da912031400c802403c4110380c00c00000e981e8a80b0419 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 159502517 1250 159501267 159501269
    0x5030f0f0d030207031b0606080c030d0203040909051f0902090a090b04060510080d03060f0501030204031e060216060b19050f1201201315090333020a02010510 70
    0x161504400e08001c9038a1096000d00204c501902d00741b182e0342081c880f02c1c401d070096641c0c2030b641561248070a01c07168004101d030f0404901d040d001803095000f0488002d4a034015030103204641d5446010352028007404101c114a0320010368410003084199031000d43c010264010201d00509100700025880400b40c42030446158204501c106203a44940ea20001050020016441c54070041004610001c08115110a4508a44002950b1403c0000403000700000b640954109401000140005443c541c0c07441c1110a082e0039a0042c0c050524001c0301900405481d2403045003c030111400b03102d02900810711291040e102800b019002002d01c0324191664041c0c83e030459041011500c10782061001c3c56014550308000140d640d10b61644588a142c0e00210518620030110f56008681d084a014000800c0200c007189504403a046019201d0502484054512060103000d8141d0102407000d030034102d603c00c4840580042c00e101880025044203000c00015072070f00001982d01920104514 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 159503767 1250 159502517 159502543
    0xd030605090c030603070b191803051f021c060513050105030c010c050c040516080703020c060c0c0a0f0b100e01030203070b0901021005010f0303141201090c1b060605030f 75
    0xa01d02ea07142540b019a6034000340003184c05110b403a800081100130040944044c91020104a1558101140007000100c80740200b203504000701100b0400141c000410b900c2c12050f0036080e401110b00c102e01d51000307010f61900040d0781990403900c2190801c0d02d520210036104220b07564609100c540160701d08840090003413030303095480044035501541c007070412003820911030422100795800c07010120b001e8810a50303001c10302010300b00200340b0b246e800103101e035407002103850114201140749203895a0b0398405421407010510000e10f0051034032003030101449982d040720400c6100d07611071501c2c881d02a030840d001000c4426080e40490ba02c000440d407941240e030000e00910985003002d41d1819180d201c00e003c28198864078040070800107550198030300910086114241030792850074082d0118590ae10100e140901c20400100c03100300040311075042d5514480002200e940b44c020a4409112501c4869401c50400503001c00b004490b070032460994905401703882851059600040e9610300c034031122 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 159505017 1250 159503767 159503779
    0x70e071715090c090406080a060b0118060f0504050306071e090308070605131401050108060a020702030a0320100222080706031e050c271c06111b0d030605 68
    0x2000c900d019001660407030f0702c0e00c949030301e00701078903000504550035640b2441161300401c102c03a081c0315241c070550f03003086000c1c28801610b45100c0000d4610035064042c0d8010b2040e403240c0c00000720b1046090394040e04000c1c3c01c07540036043c01640585428141d00301450744098061200900b684a070340050112a88680681e040c180300d81e0700c010180c50700030311103040904864180300104005204200b032420f1524000182c5504003d021410b043c8003e20f02d0041c030b4010440c84d001620005003551401da01494004075820005843c15842150f8980c018001d105004003400241616401440400e1482d20b8009400d66041994801d6001c0c1d4400c1041d50780000b03c08001040c0a5045034515140080403900c611180c444108103e07502511180b94502010680a400c0a03008005080d80d480b00e000072103149000c40000f40f0b108014060700b0040305400c85008003007010b190130000b208450351509949400103100310040c04001258401450f11905e00f0640c007440c06845440300740c484c09000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 159506267 1250 159505017 159505051
    0x11707090e2a060a08220b0405010c03020301030b06060309120d0c0e040510060c050a0f060b040f0506030d120b0a03080a0f0806030717030c0703030302041403030c060403110a05070e0717 82
    0x182c070b00c00401000403140d500c008204596980c1406d00499000d403041c410300300c0da800e06042913030031503030892080400d040c03040005001041190702c40d542e1102086401d55544da03100d08009041c090ba03511505681e001c085010725602140d90170000620005503600075801034818200420b60300196481c031040501c1ca10300703200d003602c2062404121401801200e40b2001c02d0b90f00c0516140a512080e03441c01c4d502c8100d4805032409002e00c0c0b00a01c7c040d2000d00c602d041880000b506d038518207071040180045015200e0b1801c005402c0300e00c00010040c01448825540d042c00d091035404003090100080d84c4007140d0f80f1080c0501c8805000307460280c0101350960a00803903a81c00c41c0e44240307500183c40305110380288900200010703c041e61195030b02589031843c1c80e01d007190b11040301c490035109400a00c01c541c030146e4005001030784541c05203001c031100ba800711456820641c614101400c640200e02c03000c50510b9184c80c5140c0170340300039951041c80290903003940312040c006440c01410320802c0c441d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 159507517 1250 159506267 159506287
    0x40206040504110c070807090501060c120f090b0711010206061c230d03060602010605060405090627040302030304030206011505030604090809040207060f0c050a08011707090e2a06 79
    0x1028083c1d11550049041c600315165115500d03003402648102007075440018107000400741401098010216810032018058190303603042100391444501d082017040c2c1e284080881e61103801e186c4000c00c580c0a101da512641c504140d014844c3c0b40071014007521070100410414204442405c00991400300d002184450715500c0d07822100c1080421084035240300b02000b81402c0074405201240c0c1d0540740040c40524103100607080d1206036004501c80c201c02c3c4000c0219480d2840320651000c2c0460361016100500000d803841380ca80f6200c1900c102200e00c0c100000c16400100460040e8000c3e003c075040b90380e940c401c42c50909a2840b050000440c180041812400c06811841c5070301c0c80744c0c8109040000b180c000c9422600419000da505a0b00c41e006203520070032912a001c225421854050b18181003000082c000d00010322030780c0740700d10f40c0303e4604000d104180a601d014003540740301407100c4521500880e5580f035807050301052003500d0140301303204907602e10045030b0815000b078161070510704291 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 159508767 1250 159507517 159507521
    0x30c0b07020102010f180b06040c140f130e0a0f02130b0a020a060c17180c1338040e0c01050c12030f1e01030510020304020612040b1e040206040504 65
    0x30904906542d01c8540c3c4210703c480c640074000e090080d01d03003d1008280355003401e078442030700503011034011894044001c201e0b980c000c0f1440d5141c0188140700e5902d070a05124408c0c00e21070392602850050352000081510408411880d001c0c481c00d210511440541d40c560b0004ca04c43c0c0c28114880010003c0b08210403640b00000c2c1190310460b005590703401c4a03540702c103800c2e100c403420080000703011001103441159001484a4102d02904e0300b040a03400115026661508032103a004e00c01c2c044003100f20710000d8030303130031802c00c2e104c2415602007460b44408010016048000e0088191461719280c043e003824244651030fa4410400002d040e076800c0382e00103584540c440a54480f06000e1000c03200d0161414400941c0a0710b15681c150b80e01d840e005043c0c5030150900c0710f520f03c3e41c1c03044100420104078005001d6184500e20203005030f6070345443c400518244074408858100d1201c41003000309010030900528444c00040900050903640c19482c14940402141d00039440641488140b2640c1095 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 159510017 1250 159508767 159508777
    0x10e16080d0c030318021201061505073302130501030c0e0f040e0f01111b0613061109090a0e101e0506030c03060c0406030c0906120b0105040b0f0c060709030c0b 71
    0x841740b080710468050300442d4074145900b05001d40d980d100d40041180d1a15a0450303111a510785c98000d013040704a81e42c100c2c1074802c0c9260401c0a4481940d60041104017541c00c10100071903203411940d4100039411307101d40303046603c070b0b0501280c5080e054035401030140c1014418001c0003445411a0707850f00040100401042a01c2900352042c0c0c20900e00c07406c024441c1340d04580788043c01310780703510038058450203034806201d400106400000620034664400c0b04244c011503800280882c400c11a40f083ea43c00f40a20051264800201ccd170901064244562145800d90b641c1c4c0c09031801404001b025006690700404c1c07441484030130441d96203100b680b582c86103800c01001420f44241d00c1d0004006440c003101a40c0f41c07000000c0000701040f000d80c1510403545258542e081c01307046d0b03238030307100025020800c107141540c4103079101d400d6603800c1c0c2e2080c002c403006081e6200005480794040d10321072103250001c0340b6050f0144950004581d00074095040202180c0d03105940c0c0300f2290030100380152039009 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 159511267 1250 159510017 159510041
    0x519050102090301020d0203041e03050403080c030d060303170a02090f060d0b0d0b090c09070507080304030905090a020c071202100f0306120b0a0506150306040e0a0203010e16080d0c0303 82
    0x801d0040b500141d400380005d008400d00c030700016031603050504001d10381c5017510b240b44074881e42440318200080e070041c0c15101242d411002c0b0302e4807544042d601c681117102d40312507140c05920300b2102004051b00003106080c903ca0990180c1140ea8516548400b00c0c8514400a80c0c002c5e803c074441c5034245442c000408009003491004541c1e003980078041400360100c000101d03440c0040b0000c00c2002e80b020401c00c00d103400f0880d20482c2508101501030058418890040c281c0400040000c0916004022010080401a0108041e850b00503982002500840e0720414103000b1010001814213100300c03e00501d40d0000d081c0218003400020640c1c03081100140300c4103264032104005141d0b9001d103140298140100050032030780c54030400910881c3c90080529100b403125040041c0011f98840c16a41d0080d0107960000d0400143c00d09940b400b01d04840c000d50541c24040201003025012034090340d0340d84061140c6041ca5244d140d0292500c040709a1000005c890004c0c000200740f00b50485417848203 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 159512517 1250 159511267 159511271
    0x1021b03030c0607020f2422150c021504150c02120a020102131d04021c15061a1207030f091a04110a0803030f0603120c161205190501 59
    0x10b454545182031000840d84540582c0120380c0c0d00504901c180092515211481d002c844000ca01c0e840302d0800030009001038480c8008000030180050840700c42c540d115402004141003403403c40d003c0d00142c041080701ca001806190300c141030820740c6183c894052540110500c502c00f141540407001041c2c440007140c00c52080c10b2840c10007482050080005594aa00141c0c1d29040c600b00441d0040a540c0010b64200d00b407207807000c024060b00110740d0003a5048032030300084d800815415228008015026003c40d20304803100c0d0200100343e01c0002103a50a12108a0100710800c642c0760701d006040d026900340c0840000146002c1c400c0d8028038003180800000108581c103510b4034504503200d6107110340d00c420a00c040c0801e00482c01103001d18481d0859403942c64a05005c0d01c1512400050404c103003c10800020502c02d660600204c0d021800b1806c5058a0782582c0b0b907641d595002d80100300e0380820301d00b10301242079640b00881442d55600100101941c030179402c0701c4d01c0051861002030b15595 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 159513767 1250 159512517 159512527
    0x6030b04050a0201030501060806240c030406090f0506030403080f070228060501320301140c04090507030b011d03120a09090531140703061b02070501021b0303 70
    0x101012952801940200001e0010600340d100140c1284c0040c0c006400b4010f1240030004507031740b080088a40e40140200402940c004800551000d0140c4120142207003c007103804681c3c0356102c2510002c444c500002c11654640d00c000348a1184402d60700500010042c80009031410409400c05410404520450f040c9580d054205078192884c00240b10b00490000064001c0c82018018640503105140400304407201004481c0c11150800c0544000c40034207a03500001950298486104a00e81c40c1641001c0e103001241d01180e684540540c04101e407404e00460340c03451280c40380703007840d82041e107404c0302d081e01448041a0700205126174030340c18422010002c0550f903120b0701400d09020340f070301c0724650306003806250000d40e800103003018050701e03108058030814004030100c41403018000905c454122090f040c51107000c0c1400340703890024420802d0000401c00c855211540302c0300001d003062162898400d00300e03200d19080c0b113803600582c0300c216803802a5084036070780b0380d9045004044910300 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 159515017 1250 159513767 159513773
    0x3080c070c030f052406101707090305100507050301090f0b0312090102010c0221090d08040b070209011403060c1b100b0a0e041703181507180501050912010603 70
    0x2119060b001110440e00405850b41003040c20405981d00d440503800411004040c240742885281d03004007924030404a107036010021038010541032040c0d07600018407880c40d10f088103016114581d240b20844451003500035000a00200e4850940a1020341d61f51914592a20010002810718075900500207651842d840031142c0d81000307071458000140f00c4140d15a005075001a08460300400b19605640040040d42c403040341000c00341c80754080000c0882d440e451403c01003180c0301d41c45034008019040002c1e002c03e80c2d9009001a0503030a01c21624071010340e80350704851002c030907511111a00355100501040404d00c540000d42015070441c3c1001c101359882070145450004280085210160b44091540081c144461f049000e401280c00300380e102c1c18250754840745c5284482d0b801240303403c0800402c0d64446040844212150307024103d954128514140d0341c0040b0040d102c0da004902949442c04000ca0954030710303000c55a050312140d0821007107000744603010121003c034035441e55a4500109c00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 159516267 1250 159515017 159515033
    0x60120030d0b010311070b1b040b0d0c021e0f010b0a121202012004051c08040608100b040305100605010f0207030f080c1203090105071701030f060f0f02090411070b010303080c07 78
    0x3403406141047c2c202d01f07040c070407025842903100c6c51002500007000240040c06040003161103000c2c03500da002500c0c82c0c0582c0203d040402030103101183d1104001c40040740480021074150390700c0303164001c02c04401c1d900c0812420103081d10414100020810b4284d0100f0340b1201082c205004600001c1220112810648241d134800c030071040e121a03010070248000c1c104402084400c10300910200911411030302e418230207005a200d05d008100c20000055a4030183c80c10307000003400f880000d00d441d1a141e1801944030018800e004425500d8400b00203641e46c49102d00004081654000c2c251103411138550000c010038030340041e5040201000308104006042200c03030b4a041041100c00d4a034209203982c9829200003620f400c0400401c03102d01c071209909484200c0c11a0740c4600390030605011850950041e01e040d001583c45940b401036100030650054000309540f4504a400708011164410b034030030070303000300b907005007500030b4450041c030029004008568100703280c21401800d02d81d080d9a80c4d80 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 159517517 1250 159516267 159516277
    0x60e0106060207030c0b030705070803070e1309120e1f020c0307060224091506180f10050a0e0c030601050408010603030302280f0e04020918060120030d0b010311 71
    0x700503440400204144040c86090700301801d00250301c40e156003041c400050580c01f45200140c05044000041003c007406221200d0410034040e007d4020004001d0100c0001c20041e070080d61901070005001c41c450344225054918410002d0020442040018044d420250301e22411800d41c80391080300b1038142e4040001c50000d00c0750b580104181d007101c2d02e417180d80c80b070f07810001d80b030951800052104604001c0b80200c00c050b081c031070751b02043c1e45540004507400481106001c48107048005d00c010075503502d00082c030504070b80c44041c03140b950340d80034401241c2c901d109441290601c0c101240380603845100640d008801450203608017501c0751003083c01c540c0d0369401240800e5000a0300c080d407201029251000340004200740c2e10b00fa41c01d0783c000d0300000c2d41d0568141003101c000c43e20081ca581c2e56050b0303074541c1c07030103400d1210040c642e40d8001d00f80c01c1c054030418003007540c3d103042031160800007081805540680b4041e50510080d08038030405001c0e018646410305803501c101c92034825440c1c010b00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 159518767 1250 159517517 159517529
    0x602210108011b050c0703030807030603150b121b040c0e0a0806250e09060616030806120303010f0608060d140307030905030105060307030b040f06060b130807030209060409060e0106 80
    0x26001c80419040c01c4181c1c09460444148613041c4811524002c0101c0c0c81c4045a0305070921550560710760508030014403a0b41c00007081c00003510012103136840c0d10b80c0050404003041d21b0080444031402100c03030350b500010b1180c5041c041d9810440015080c142c215400c1e03c11941404050702c81054001042c00d60f407500300c4820b550003001009100008541084650300d031658032110b038000d92071002400ba000701c40f000f034016460900852400d4540d070003150288075030894800380790f00042c50300030044e201c291043c034410b4445c81d0b2207420b1a500071088038100d03031291a822445510f41401a105204001d2410303502c041561800ca001c11000d0f1080344041840b48065599400c140c500641418910341105029a240000f00b00007a02c0000b07000c070681e500850981c500707954030320b0151010034803d24000c108a08001e0000f8100c501c01c80900000103440c12300c509465129144223981e415680720203544030842ea008038400381040d031311200115001c1d880114046035a41c13992803c0d10090381c0302d6 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 159520017 1250 159518767 159518771
    0x807050f0705010f090b16060c0509090121020d0303150e04120206041e110307150801090903080a050403020c1503071428020f070e0f060f0d060221010801 68
    0x6005200380038405080502400d08003c22032090410000b8161002e9001c1c0005002000074240240351361860590b4216510100a000c4510880030080040e00507040c0940120305d0314001180101910071050941401c50103084200f0000741c0030045154101c03102030303090694802002c00541184c4240700e005c2c0180c03c00c042c040d800e03c0e24103031112480841d52082150000710900000800c1000406204242101403500c2d420b0b440c146043c1480c56441140d5151150280018070700c11071440b102c0800260f0b8a4175400b50303a0710010303541900c90b03030b00b40200061a800001000340302c242d07004d60303045402171049600c040c61a07004901c24110322691082e81d0103001c01040401507200700b10004102902d0041c5041482d002040103800300c100c648808118050341a90001500c01c00540d9480038483c1c0894980c26a0f4024600c5400780030b1383d8100c04035103200d001030024103103240703440d0107070202400c044040403071615100000c2d0404044250176244841c528405410b82122050103001d46c0000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 159521267 1250 159520017 159520033
    0x61204080403171306030b1021021314120604020607170d06051003020421020d05060f04260a03050c09121b030a0209010303032c0109060605030303010b04090e0307080705 75
    0x20300f441a442c0354060000c041c20410608507685420015a048c8802400c003107101c0c1c8007880c40144209000c0307881071849031010482d00c8449140300441d5040b10646081010b4402e120b40c2800507403026140249490b5000e80b01003001820040018140c550280003201c05884054416005583c082003c13071840c540c541100b80900e1a000121070611055030a0444c0380618210008207140c40801e0301401600500e035680c1c0c19500c8000c012000c103680003084c2d5000340b91011021080c0041902c040e82c04012044044c0c6080d03084205e0200d6602d2000005070a191200d68201d0160500400015895205010303114850b20b610580748094500b1a0251054514000c9801c1e400000a080780b442640560320303c8000da110500010305481e0145000701c0c10306c54102400801c0d5401101c0090032134104032610a080006621082035188560780900c012a9100f04060f50382c08203000e0f810401000304000c0100c81490391140d41c005400d001520300307100c0c0c1c0741c46a68452b004040706964582107661 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 159522517 1250 159521267 159521287
    0x601120c02030d0f0219051e070b0403091a04090c0207030c12031101090201050313060219051207080910020c0c04061e06030204140f040b0d03050a030f02040506120408040317 77
    0x42c0300c0c205522584c0c11400c000c03030000d04080f101c80182a039001d01a00255002102c00b501242c00140001c440803d40d03200c0c0d00e46440d94401404540580000d01d18240100c0c80020484846081000d809882404c29040000140060001240081c00c2d48900b0070b0000026143e04c100c02c000300400700881000a0060074082e0002242d03251541c41350f498002020010317078002d001d51390001440143c81c040310780305141080003403049901811141c1041c440d1809001c0d445001003000403000d58030750000b5140c2010a0701e03c0c94056074803000a030400d003104100c03c809540a800081060740c1258800304822001c1000c41d0410341210580d075005c07146d4003103080402e400d110028111031400f10304e05440c3c000452804600d42c200380b0700c110080c0101001d151f503960054003907240e00400105044010349006001da0703010410100119090840136990b41c01c81303100307035021283d0180941d4641003101d104084030844c000d10480e1a039206110120116000d0100c0c420540e40e0606002da460481103 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 159523767 1250 159522517 159522521
    0x6180f141605090106030518030c061e0702060412030222050a0e07090302010c11031b03010515030604060c0513080c040b040203010b07060f02040801020a0903060605030303100b030601120c02030d 86
    0x841e94024070456940070072980d01d821201504558840c0780002d03081e1107031498485002018103080d0384610012400c0ca16007440401d60b02e0042410036000c11103000c400c0440b011226003250070b01c01681100b0001404200304c01d4212800981516006182104100000d9548441a07401c5818440b00e071005101e24180741c8020b002038041c10b0290fa10524040000400bc03041c2d60000030b0400083c3c1106108100c07002800c000c0844009050326405481052107070314181510a150348651708080216010264010001900341c00240203040142d0f0340d512864003819840300d0500030094200080d8880200300c0a90202820500d8050219280d0800800c420745406126442c0f0462040004024a01c0c5003411201081d61002021900044d0000480001c0c01143c1c080d15455000058442c0e4155001c0d00600035284581c04c200b02090700d038030500da900d000460380c5108001103403005101c4c030743c11036015541c490300c14034090400304092401c032001d80d03160a01000160b4004664890070b01464 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 159525017 1250 159523767 159523783
    0xa20100c02031603051216120206040201030615020309011103070501050103030801080d0201020f180109030605010f21021c1b0e040b0601140d090501021e0405030f060606030406180f14 81
    0x21001003540f1038150345899880d5840603010040320480020030a0084101c5c5a5004181d034200e0311070744a00059400c044d454000c121030890001c3d00e0301d9004144d54440d6000c0c0407010080358000c500f041030117401554800d44145454410344011710500000400901606001e1442555000043d500d4000c900e894030030521200c50a40e4010302600c4100803220b019140e1200401c030403401c100f1074080c0142e03034460392a08050300c00d90500d4000b09080502030091022035800d8031a540c9060709000e944081400c9600000358002d070303044984d401c0d05402c04510800c80d80100c02102c0800d0150712030174181c01d480d40c01141040e00980800061020829085510000a0030007141030340995a00c00308074402c040460210660b1030940c00d0a206003541583c0c1501c04c17944c8005010190394940040a400501c10726210b071040400d6540044c0020441a00600e4060085810f540300e40c7e0b40c0802511846006440000b001301090f00410440c1c41c1801b105409105442500d50304c2d0310320b0900300806 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 159526267 1250 159525017 159525043
    0x902120c07030e060912010606051c0203010e06010521041109070f0c150f06090204080c0d1e02120312010906060c0305030f090109080f030703060f05030a20100c0203 73
    0x14003000c1e012a82128880d03414400840d041a0b4172000400004c40710700c11031640c414650710b05813001c030301c150700100100405401d20380c128111b0240c6001240c26031209010b5410150b00f42d40100b82c10b54040c034050414400f105031640b440c60043c2d40c0744124100d0480e02914221841c515940c003609120500d240c00000c107180c1000c000550840140c20b106600390010304000807082003e82c40c0c06c6540c80007040005002c0180a00c9580d80711181c042e40050048285a004d0075400800a1a19603003551540b903102c28132442009403c1c241f8001489840c10a980044450186080c1c1890510043c4080142d50502a68035410b100a0408841032070304003034240300c0e104e1400c4001c40e801101341c0b94841d0710248861450390782e902c001c0d405080c50301e000500462000c07450318000c14810001e184a000565020042160b41d504102c0307160000b4401c05030503810003528540030803030011340380c0115000140c03403052060340100412403104650030113400040c0180e0703c84046140600030025190720f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 159527517 1250 159526267 159526291
    0x603081602040b04091e0501020405030a0c0e100e0c0c03070c09050901060605030601021005100b03070909050603010c050912011d0106060e030f07060f0e060d0b030f01060e0c0f0c0304090212 84
    0x1030354802414503180451107243c415400c4006e0208002501201c0103000080c0940349241c83c186801d0880c43c3d81030060030807111311035000032005d580d46000302e0115640c2008654840d1140d005240c660b40c0301d82c00c0398410340000c22942c0f000c00d0130b00e4031f541c00401c40040b000825180080c949400c40c0d2440d00044100318041090000c81d0780d000a20740c618075608100014182c40d92506160341c2000790f808151582000701c00c12694941141c014400c89901031003d00480d9030305e0003090300700d541100442c0040784c001e200c0072902c2d040c040001242040c0320070000a0840080301118001090650580e126a449170414040d059110060307046c8c480c2e06800424010310301100c81500c8091602860003041719840421440910980d903801d4180b101502c915520034003544103070040e11188102c41d0107440b4500d0399581d040414030880c2c3c201e03254444144159140c08a6410840d44451501d00041c0810700528141c80d400b800100b00402c1c4071036005a442540c00901703103c1402c0100030a924032 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 159528767 1250 159527517 159527531
    0xd0c030c0e2d010b09030106050a030302010e07081906020d0209040510090b0301050c0306060c031b0706080601020f1b0303040b0c070501030c05030f04150e0609010c09090c051209010603081602040b04 88
    0xc0308500c9868107513406500016102c04105010070300528030395010340d9000d05040800414540c0660184241c00552003d4455040c0c44d820031954840b0103a0603c0c0f4000e103640b20308004901d040d03010b0070718031084600c094980310f60100001c0903520280c07060304d0200700001c000c00500f1410b01c114940a24164000d11191500320040b6101c1e0200800307007406000c1c0051303500440382c0c2c00d0086480e0b0308241c011103040d1030140d007003042c0e0784c100d00d0244d40041600307440803480b1580002030141587c41d034880201080045101d4400c0e0b000c00704070000d078041c4400d000c0426080340d00405081120036080040c5419840e000005054540811400341072010070410310502403018039403160311030780015a145046190300c803000000e00410130074202d54021042882850801034010341c82c0641c680d586c1c40c14441d10703520fa10040320b1440c010000416802c0103c04416016104165488403186d40002100380e5682c0301c6003280d5000110b00581d280909607902d04500d410311501da6511410390f4100449 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 159530017 1250 159528767 159528841
    0x20d230604061514070c030f0c0e06012109020a270507030501120b09120409090c210b13080304030512100b030604020304021906030207052a0d0c030c0e 67
    0x440c0d0403404111201300001460000d108540d86440001c650216408440003034908061200340710718050302411402c1d200114041c0c1d8420070244c45440c1d43c468090888000502a40008114640d012a00820213030f0b0006148811114003107241540c4501025041010840880480d00014000c03010b0501d40750040c04210701c465180c00404c0c0d4450003124280d01c444404a10308400c0a00861403a000000c000c5510b0419401c030800e00d61045c245040801c0d00d80714010030844290f40380007060a0b140c4030502c0800c002e40020b0350001c07500c00c2c480f80c101d00e05407a10019a801210103401058000440c20000b00d081000036602c0350b80c0100528050742030040c104558400546510310864020002c1420355480059840940c48104260904030307981c2c4101802a420000003628076009600c1d5a40c41904004282008024807024107079041306840108403450940d5401500d12110781507002c40010b54070070f4800082e090000c2032441600d00355001003612055038100070b2040002412507044 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 159531267 1250 159530017 159530027
    0x20a180f0312020c030604030906170105060f0a17040305071403030105060415110a0c23150703050c0a060b0901150905040209060d0501090209040e0d0e04020d2306040615 75
    0x1e4a0740941e0032a64119550000c81c941019101801d501d40180c0d02031008141e0423030248400c903081c603140c0070140303482c021040c40030800034400c09401440802403078400c1000302000305100862801c02003580c40642160000008003181c00310f000c1100010001c00740084282d135017281a07203040080d132641d03061001140940c003640c4607806c1c070aa01581c2481d01c0c6409501040d081c05c0380942100c2e03082d002c0e07092400744101d15124440e1003d008a611017202e1120707ca0702d2001c0a4090410240480310f24411980d0340c1c0710003419410000248180ba91011051281160b07480c05070b14041032008403c020404c5000040e406051024002001e54601c40d4000340c41c14100e4100b120010b880da6035640c0443c40c644a201880d203100c2c0c0c54807002103560042a4084c1111070400e036410000d22040591103682c0c0d80048240b80d012031114820596246855002094009001310021502010814100b81c0040140b02c40c9440500400b007001103506081c8544070080c20700e042d007144008940000a44 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 159532374 1107 159531267 159531269
    0x9020316061b081b19050102030702011a0906090c0903030a03020414040b01050409090f0f050c0907080105010c0b061503010b030403140301210512040603020a180f 72
    0x429041841c10118480e950001032580b400750300403480014400010301460300341c4501e4946174540203504680340c5000c0c1c0f0410001d6200d0520081c00f909541c0b204000e03c82a171007184008075142d07180b982c038640000058034581943c0d160340b0114006403280c5484160544030004035a00705a9059008200300c8446142d00140c160700041000183c48036030b0200c90019000b48400d2114985a5020108891058070f541032803145981d100c0035844000d8605580c150070848542c20345043c0b00c08000d900a8243c58103140071f40c14000080c00f030340c618042c082c015148030070009410781c076040740c44501104c1c49800301d522503130b5507a0304581ca6401141c0840c000b400400d104240a0030003820399060b1020000402a109201c111702e20409a800d04140c0b42c500c241300c0c50001140d4050014000303041e0a9501590b40c02100002404604a81c91041e036210240e65040040350074014940c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 159352517 159532374 := by
  have h0 := BRFrame.cov_init 159352517
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159352517 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 159352517 ≤ n) (h2 : n < 159532374) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
