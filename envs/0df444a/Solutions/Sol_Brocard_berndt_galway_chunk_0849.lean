-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0849
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:09:06.455492+00:00
-- url     : https://prove2.me/submissions/c4a17793-e701-4f7e-ab1e-180004c7a9d3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 152517985 ≤ n < 152697841 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 152519235 1250 152517985 152518031
    0x414040f0c080c06071203110d021306030b010e0d03090513020c070803210c090406090b03010e0d0c02010513050604030506010905072f0a0b0709050312160206130306 73
    0x681d48101003507400d800030304000d000398003405403440d219054940e103402c440740c482c50300d04251711000722080001c0c5800292010300a06800540c40d5010300c050b10314030690581112007014034150a06006a0b884546442060019a00c500b8a04044e050485845119810864102650521030683c500250340100b180c0c5080409903000c4a0b10303041c2160b2a0710801401c64540600d04007060a003111a40c54181c02003a07019510b864404600b003c6030a4a400e540181020369440030950401e05080c044c00410740007580184c200d1040701c2c030001d480d005c40c08038080e0401002003650790540d01000002e401800c0018255901c0310703580d180080d5a04024001c42007400d05088c08035640500920583c0a50301d0001000310202e400c800c0301c0400b4401061044809219015075100030581c0c181103c0d0181c4010ba0b9440e8110f81040141032418002d007121070348540d0100030003519000503040c050344055048078900d45d118103600c6000c154800390b42005d44050700d0103610049810507050710365a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 152520485 1250 152519235 152519243
    0xf040305010f06050105031603060509070507021c050607050f0904060e011a0c0c04090f02040e0106060f090e012c09030a0e04020315040b060424090e01060c030507020414040f 77
    0x402c00e0440900c900580f103091003000d0200341c06002251043c00340610300441901c040c5400202155517900145080205a9001d400b1079000102c10065060a102c00200d8096014103001c03890100e07680c2c60b03035a1300c000745032034104000460803041c2840050200c405803600100144282911888441c0000c642841126081c3c560b140b825481082280c1c10703182450711440142141310850424072001d44031b10201252200c00300100a401645c45e40706174141444411b000050250800c000035092072490542281880f02140f410040320031800c8080d81034454000c4444003c50450b01809a09058403201c401c00e43c0e41d10040103184e9000102800840115030764002c013200070081070000b248801d45000c0351000741820f10107154145034200718030341c92024010901d429a144c10400010941d0b12511a865032450080490700c1da0010810b006410003c3d0040015450300342c01601e0046200b4006046c1314020451600355075980d4400e032450004031010310203d2400346460380107070203a100111 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 152521735 1250 152520485 152520491
    0x1b0b180c01020613081303020d060e010e030c0c040c020f0a03050a08070c050a0201030c0504080123070302041d04060603240f0b030a141c0f0201050f070503010b03070e060f04030501 80
    0x5540350300c0050514016400c00d04513040310102c50f110303119103601000800051102d10000000182c440f01c00d003000050140200240304010341c0d40c1a402d41742c031850080a207510a00c9160701d4420040703000040340008071000260308000d04030903828486124040300c018010f40300a1014150010010b00c040e90700c1ea9203144095031100000d440c0300c141e032070000d00716501800f80700006501a91185011020b0750a040c1d00b05176071a0401420b494901341c5000000825038482d0340704500f04104d90303401584500f81076040c1400e1100b001d541454189517011448403a0740440c091050716488600a1a041840884400f00b100e000e080700b44111020001c1d42480c0070301c0002404001d101c1d0b41d02820004002d030810704043c1e141c40c0030442d4018090030130781c0200c104c42c45000302550240e4101360055107680410a841520103130840704014005089500c1d00300c20019016402400c490640b203064902c03079125111001c0894511070a0001d46400c5940041c001011400c488003034006c40344140e000b4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 152522985 1250 152521735 152521753
    0x1021c05060102060c0406032c1005010e06030a03120b0301060609050108060306010614130b03151503101203110a110a140a0303032a090905060913031b0b18 69
    0x499a80384c084580c1e030034440c2c05100c1400002e00c2504451050740c4088120144403000d0130010400007164415842140d1055442c1d90340880e05004150051160500c00c05062810b040840c4e1a881102030007010801051102c0d00d852205501034800d0050244c001c11105445080240038030060780500e41c007207510140051081e240000c0c50b1416a02d1070b6031804c0d4240c0c6811261280398101800d00040280d06240101302907000001440c41041d651480c0340e5101c08890174810f40300303d070300745000b91880100100602c00c03000740f07411001c42e0300207020001d400804d410120b64a00d2030400c4035009000d040b01250a0104102e86800042d0003250744000c41c6913038440c0160352010080c0d0541c4c1046681e0720420110380694041c0884001c030300c4c9440c05000b0a001c20700001c0c4030814040c8017155580c6000d100054451203000e500940c250f50101841c1448a03400000c00f404040050400c109061001010281c03400303c14400c540c00b40860076941820104030355078008100200c08684201c0c120 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 152524235 1250 152522985 152522987
    0x312121406010809031303020405060f090a05060a17030301051e0303131403010e06060607050703051912030c230c031611040510090e01020f0d020a0201050604062303010e01021c050601 81
    0x880f086e41d54a8083c0003a0a4556400d1001506009091a91002440d01d55500079100d0184042c4108414000000e01e03203440e00800501b807081e5084103c80001146000e0454980001101d0560b03c08035050031090450085048212501412017509404045000c030b044c840c8072140e140658100a8a084c105440303002418200c030710301713015203545500a201081031401c1000081200c02d010741c0c1650685620b07910b8035450600b14000c00302507000b603140010140540006500040840340c50b06210422070740d01c000302400083c1d04d0000c003c946a0500c1001d004000044030111002d40d010f4940300d0078a89034250381c5101807113040c1c0c4c043c103500c11422100c0c9480d2003041d2169a2007901003941314204411071005009180d15102d6035075080025a207050381d4000a80140003c407900035035600c050120003401e480000c4d040c01e016504007242441300740e0700c000351100052481c540c5031000407100c20000b400b4040703901240f19903503c002401d0044210b04815205406002c0000f8000c90300da07400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 152525485 1250 152524235 152524237
    0xb04060b03100b0c0c01080411040c0c0510020406090603022109150a0b0901150203070534050f0103020c03090406030605011a030705070b07020a0b0c030a0e0105010f031212140601080903 82
    0x4425005401c1841c105c8415130103021400d0b00a4002d51005c01803202210210b0102c13010700300b4000c045a010744840041050400980307514a1000d1415414640b4240024040d00e10500070b0b44103140c1c0200d424000c0d1310f1a440514031030040c15800401a042c4500c0721a181c11182503406034800c41c81d000555942c42501039001c0d0210b01074803c1e0b4260b07180c50654001000045c420404501040104101042041041c0403140c1018804c500120300045ca00c0504042d5000c1c04c2c03103030030f043d401301007000d6074440d44000c0d0520400e080c056070340c00340c002209056100c1c642e08950f0013460044048144084c542c443c606030340b8040a50750030103500411211a81c00104ca1210018904115030300c000303925200030907000301460040302c680c42100d60741d0f600d003203034121800c02c038400000c000c10140706600d01803035140041c80c100801581d4106100800b40c80001d01002c0c01c0340940480d026045e5220389885490320501c10803c1007410810110b074101c6007000c1d24214001425040440c0300010040 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 152526735 1250 152525485 152525497
    0x301170307050604120c06020408030d050624031b0d0c090503030708042601020a080a15030804090e0c031e06071704020909010b2101051b0304080306040b04060b03100b 74
    0x90000d241c655210b980b001d80e6100910840c1040084200311b0200042003400a400680440005540c6880e0160741a0046540c000c1c000b610440c0341517810345840b150707000f406803044d407034048440d82c80d0b944002080ca542040e050081c544000051485012561944452881941c90b650480090340d03940030595240651400900b01e0f001c2000704020441071016a0f0b840301820300c4101d588001c00721840c0d422a0048502400070614090401c80031002612943da040d0602100100083d13041d500d138284c490207036001c1c801c04255034a801d1003441c0300403c034801500c04c2c002d085805a07061b2040f103c090f1009101441424419800030078403241c022441880c2003148408654000d544503001c0001402025116200555039001c1500c4152600c0100c00001100205003c6201019030031587c2107980c000c1144000a02540d0303040407002c840d60841e40c205401101e4a0b0f1280c40d040b000074002c0443d00006c03030788286007400000b010703042d45016601c150324022a0050b46642c40b40c68050500c102 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 152527985 1250 152526735 152526743
    0x50a0203031609090f0203100b0a170a090b010338070f0915170a020702010206191401151e05190c0b010801060e010b07030203030402010f110a0303020301170307 71
    0x14000614503000381011500400c14603e800f0032080d6032200c0c20403c84004030300003009250000100040d0080900341d080041500c849154075010705824014103a0070700384100109006110f01040b030440131908508007903504500004100d503500c0c0f03001050301c100c2e035021040b80c01320002e001d5000007540f00c032500c4000b20007128078510750380e000c012511511410040c409000c1034410105000034494000c0a403000396864140100400b0011141d000c6002001e641c14640100428030050360301003070b07850f0442c40041158456000c46064000a000c003c0e07510700d8038089420000a02c80ea40044070000309542d5140c10608402088640d01c1d000040c1c03450502180c01000414003810344800342c602c841c112880d001c10040c1070360fa80d0030030318102039101c05d0003a03459a105100980f101c05e012801402903c0031240f50105c190740182d202c0c00001c10180c144400d540350082c0312800b9400d0980721200d000241c40e01a240c2d441c0c080e009401c28000e5000754100081e41040040001089903600385d04 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 152529235 1250 152527985 152527987
    0x120c031403040c0608040f120801060e031209040216051b1e0f33040f0807030317100308030a0e071403030414010516030210050604090f0b0a020f040807050907050a0203 74
    0x81c51000c5d81d20f5080680210f03070b0112007018220200c0c0a04183c4800380c00c1c80da82d004040e525141005200c401d41941480c07190300001d100140b940c86150440301c802c4170a1f580075840b40141d04c040c0741950054000038119008500c00c11500904d80c42080c04900022540307824001d06840c12420058141348d11a03030411420780e00d0220301d2510b040e103002101c41e842e552900802400d00401040b400c030b44206400e8820105043c0049100d003c00840036010714030003840740b6482e5440c000d001b21460340310541400740c404007181c40c4440b141c4644c0e01440c3c000f20300d695a410718415010043c0188007a82406000d00c5038042403100021804040003b002801141000c0c24000e14000c4108414291414088104004444d001c4103505544800f8080e401500d142e1841c09110b4040e0b5800410f001d00c15481c0000d11000a4400c019440d1032507080000c440c416501d1080083c006e01c05c0982040c0d102070003140020b080e03070b40014000305580b4291403200240d01d81c20000d4a042c05107403903540c00750700 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 152530485 1250 152529235 152529239
    0x506040201032a020304080f060c040b09130207080d050610020d03020315030a031101051308040603050405100204170c0f030a14070e01090501050f010f0801050402090409120c031403040c 82
    0x22103034000540031501103580400700d0440311030000320f5040450b82100507070008a801c000c40e010500281120030b40300750150113145000d00300004584501c1c00340c007450260100d0404808e403900000c8102400c00031400315034440203414506c1040d04900f510084090a14000401600703005a41d42c04290880c0c0090002d5088a0002d8000e500010140100006d203001d002045a5081003031900f014080d495804007062184501402d40c0c030001e010f90002101081c6820000b40044100c90894025190004254440c0d1401c541414645901001054008180030814050744040750004c910060111254801130005000c011049c9650155050b0022010000410607003680040c0440600042d10360654a42601c0c1000750700c2a00445141780d65500103000d1820305000c0c010040109007043c140703014a02d10300400c621014003070640207a80100d052911915941c0000c0201c0d40d00c00010303d0441607001c40102030441d070b003a080d00007564128200620010b0304084134040c40d00201c051100300c1c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 152531735 1250 152530485 152530487
    0xa0905250b0c01090c0308090a120206040308180406030302010c0215010b070f0f0803040606090608030702220902040207050607030b0105120f070e0d0614181b01020a0206030a020304031b0506040201 87
    0x80c120b100511000e540319201e060014480c801d0030006148150100c0380c80d240d0350014466642980c3d0059145000b528401034096500c3d481502c0840c3e9200061716a146e4604c5071603803560b109990303000e800a040c41c60200800d6019007020a0080803942220401e074000b03401803145c10b40030310a00035a00820086440071600035409103030140e0142d04181100745c51a50b03079038000e620880341601c01541e5040c080c0b25102c0d0902a4400a00e4070000a6003880b85640016095004c000400c51098051202d8807803000141d8001d00d49a54008108548941f0f050170070381e132a0345080b0b03901000240b8100204d102503001d03c003a104015100d194216866a901254081412000c2c140350b0038048101641401d9036519071602811511400f03000c6848401c003201040851001b4100c2d28158012240c01049500000345102110f80c0c1c0b1554a030040324010300503400c2c464513640294021000104022565803140c0045014a20030b40e83c54000740c5000740580c8025620410080170758010002103030243d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 152532985 1250 152531735 152531737
    0x5010c120509210606040b011b050111070c0306060e090709090203150109020a0e0915011d0904050609070501050708030a051803190210050405060402090a0f02030a0905250b 76
    0x140464204a840c24401c00c0c002055042c0802160300b0344060554030343e004070010300159820040c2074405004402440001030004c409020460540100c60b04040c42030050135040114503d01c0400100c0c0d5a610b607080c4200c0701d980720b01065a28500700340300081c0010748107030400c1c8038094442c00742c04c8150514120303c000c0d040070181070f64075100741141c014900c0d60048440c0e008110f01ea5005a503040780c00005001d600b203038401c907480741801504224034400001c008618691007441c0101007118141d1140110b54088461150041c007690100020400005210340c01144814102d80800e59908011111481103c80c0101624420310104610103010f400c42070301300000060955400494808861954010410012110046903079a14100c0d4040c400c4184110303d45a0500c15860b0a40320581e5801010704000e024117000b400286e2400c04c0340d03004d2540049111002d40d035034205203843c40044c0c080c1c2182615140a50381580f0880006c01c94103042c0d0424012400c0d40182c68005e00d4205 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 152534235 1250 152532985 152533013
    0x201030e150c0706140106260601051935090303010f031509170406090e010803070b1f09051602011a0906040b0319031403010303170c0c01091a070905010c 68
    0x142c0e64580c17407140060740e48030902a01030b2032640d4030348848442e611145e403d42c1c80ba11400c1e1054020302802e020351641d00008803111003142c50b01042c034805000e001195070700d0f980d1480421450660249420240f0800f0440201d0b2100f4205079006440721100681c44c0e104c01e214841c41e502e03020404000007500c100c9540100580d8090000b000345c2d0584038023140b0501500c1854101030300140500c0801e40050303d0f58080d0070482c403180010340c14008120340d00c3c40b40c0702c0040c080c181d41b0700c001804c103c000307181604004007080050713660f0b950315064480580000e83e40240ea2030807240f917a40045105100d4000c14a400c00c8905000107041024840001800340807290415150105914103480800c1540c8040e4907040c040500f400c11801c0090000e042c0c840181c540c500108010404294407098591007a00007444330842600d4261140100384242540704060354204880c140512400c003045103a2490302c0240d50960303582e0a1011a0400014052365010030903400c504d00c0828501c804482c8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 152535485 1250 152534235 152534243
    0x30d0f030b120a030206041205070302030f090d020a08100f0b010215060f030307050c040c030612061119080a0b060c070612060b030f0108010e010b01050d180206160201030e150c07 79
    0x1108001d00c2205a0070b01c03c003154241d001d80d000600344020880b0561442a00800c82d00d800d50a158543e40c0082d00ca1041981030086503201041c8000c0940d12512003881542c1c2c000c2940f07106079030325500f0070384038694440010045072420b0490754203088503010701701c2444416400303050041103001c0c0d40b4005041c064401078100062440321009610304200800074280101c00512854004608100c16220104103010415060070342c10070116501c0d0b000710b102c650788001d01103815805d080b2040c0c0c01c0d000d5a08000e155034882008004110b400100e81402104404030610860341c441c0c0170302801d4410181d084440340d1143c4410070040c2d1080f07861210622141c0300106d4030b03540c0c6801040312500300b42c0d10800e403510950010051800240302c0c9080a1064170300903c0341003107181c0060214003a81002034406a1246681205100c80a0030b5440d42607004000b20f440745510550205210281b0100301d01091034035015012024002440103011000e190106955031399503011030480381c1051800311 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 152536735 1250 152535485 152535499
    0x5060703030b0405070c020a080708070e1503030418140f070c020f030106080c010206130b010b0a12050a021e03060d030c05030409051302100e1311070f0807050705030d0f030b 77
    0x444a0b9a85004285c0a40ea40b0b503121900c903d1240104000c4c1940b9a11601d543e0b4013480f42000302c00c1010410b9070450318603901c0320301103603208000c07a04c1e48085581c2490389400300040200e030080b80d8400d56510261900020031004001d080012451101a150688000030000c009004280316004129000d131018210707100041101004c207003964041e400031481504000c428104a50341008065441080b848d51141c030007200d42c0320352509100600601c01841030008800b0b110502415001d0600180c00e6000c010758034083d58900002e41021581c0001b40504414031000030301d905042d00d018020040c487e003000b10b0304e80e4007511903c0000c4000c40f803a0006000005402030740744682032090745280c0b0381c0890021280704000900c101c8810f4001070050306050751000d6121b8240392090840d0024000a081d034152204610300e0007040401040110410b506038100175469001d01300361842441110049911201010b440e541c1802071000043c80319603d0b460003602c2600311a044580c007a0401c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 152537985 1250 152536735 152536751
    0x203130803070c020d1a16050a14070510050a11070213092105030603010f05010e0f06130c11010b0a0b16061b0804020a0611070e150a061101060503010203100506070303 74
    0x30480c034411707501040d43c5154a000940340411400002203a10000348460140d14030308685020704503015484001c410054200d40045010600c4070440d4940c0da004811500c001c0d480042e904058141100e00c01a0f90317040c00c1100700004510004d8510650b4010b00a806032600803c41c000146000103003550009440811300c6494071810b03400709510a05035841580e00d03e054003c1c1400d4844641e26040b0045c40c08004210200700303c940035800c1050089010816260132000031260701c00305002003c003a06d00b54141190710f4110440009040c058802400502da9007000c10406192610680001c0d040400440f0544040d0b00c64808807a0301c00c5000180d154408034407070502c602e000300d244003c03d0a00c41400300350701c2d05002002c014170561800203800e02d8640c440c40d46541051043c0c1e0300c802c10400120320445842001540c2808011b010aa08182c1e203840007801d400c2e0700c840d5110254070300a40419030307042c180200d0703100c2c16030381070030039000c901d8a400c0c08107640c00000c064007090798607a98 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 152539235 1250 152537985 152537989
    0x506120603071e0602160f060305040302010f0606230a0f05131203050901031a06040b13031e120206010509060d02060d110d0b040e192112050a0203130803070c02 71
    0xc82e00500b02000ca91120f5040600117883d007425414640c0c03103003951034410044d0304201c09140003034407100d20340031801c0c0d1200d00e030990140a000d800540020304107540030030310326880488080c50f210000180c0c2404518044810810310440d0020000102c5480b101102d00740200c00400c0c452201c030b10a00401c40c0d0310751300c0d1403024107039890480024000183d0300f40c8a6906002d04528448031040310100c3c01041f000142c51485140b003000800c5401081d042041200001444015038010310310074018084460100d1208074150b00444a0b41c200411541c001440010524140c4201138a00a650380b154030030003650021400b4201da0003d420844c0c020603070301c20300603240d001041c0442c00d51500030181c0d030b600665120419050080c1d1a01e80304084104000030942008038840d02840340b104407504010108410003085001d80000d40c00544040ca07034030442044030010400800c01140d1100c402604c203910041c0c44010449045260704804503040700001c580282d680c2c1000f4032514103541c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 152540485 1250 152539235 152539259
    0x306030d0c02030307050a08280c0210050409050103081e0313020607062703020708011e05090106120b0702100e0d0f02070807080319030902060301090b03010f09061d0304050612060307 81
    0x202c8030b01001040c0f10b907030b03c840301003e2170100070000c22501e009c1c2807a143c01000100304040c040d109065250115282c180903500301d40140c6030300c02040c0b11030740e141d003170200c0d0903030048031003101c03407400e4404154070040554150390040356240c03105d00075507146408000f042d421041c0d003540c0450b910303150052400c4440122401401082100324030180640c1000303424039009501040380b0341d040035107100265968012040b6a035041e501c00042c16220f958099004040d65040515094488a50b200520003400e009500c40c02103a8202d69a905600302250155400300b400c108403588528041359110340100d507903111622a910480300c00c1991511003524000c01c035406080640c20001c1c1c3c54104044440188484480301d0a080c0a007404c82d90218406210500c612000c40c2c0d41d516040c8840e54083d0450400074020040500020700303c0d0604500404024031500748004031041c200461744004402d0b1802c403030000304440c0c1042460b2a8281000d1402000d541e85402100004607194076002 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 152541735 1250 152540485 152540503
    0x30804092a0206090d050c03121012200a0501050702040207030309061b0305180c13060b07110910140f0f0310021201080616030207051501090507140306030d0c0203030705 75
    0x42d0080c241401c14110780c50408071150004410002d08122041d8000d01c000100c40300b1400140380c4003607507601e000c03108500388119003001c1062503a01035040b05020040c100b00803070b80420140c4a41420800d0208080400c00b4450140802c60600412016182c254007030111140603080c041000f100300c1d5554012100a08100d103a100049419840750541c14820f10354824005100000b0050400480c00d648120f07544400303124a029905455111010b9000381e0001c0500741075094580303016240c00b085843c024480c1c18022008500021140301883e032085040f00d6505c15a1000d44403014140080e840503000b200d6045503400c0c1c1c800e00341e51010400b440010160010058540386802080701d09d101c410380c032a00141c1d02c12000e0241ea100300840c0c4215490700341c1001a910040361920504050044c2c440302d140c070580d10000215541c0d1500715610485080d9a2110700c9440031548185d01c0c0010b442d807540507440340d071054401601505d52003107031a00040881e8103000c0c45650302c0d481c2c520341e8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 152542985 1250 152541735 152541737
    0x207051e04060608070f020f06010b2a07061209020901050108090309060d050604050609010b09061c020706151203080103080a0314090f060c090d060507110d0e1003020301030804092a 80
    0x16040041d90351b031081208110340300510140c588401000351042d6240c0040c01403003104480007402400c00d5031201c3d2a01e22540d011014541076a020b05010782c1c0300c81e080d02c602d8011644e8002415480a610f102d6100071685c02040c0001d5a42808011164080002e1031214148001c0000380e0303469982801a140101e40d940c4081a58507101e000e000c25140060022030103a0407890061150b0220036094451000d010f80da015140e540b80c820101c2c8010350300c405404058400121241400890f41009070110f040404c1c50340029a6240d81c8081440f0403103000c0d000038114401440014002e000501c404805032601040500342c0550302d00403c4000d5582c0d00483c0c0c07000303213500c07a0080c042c8401684511040440d90030010310340003007910b1041e4040c2c024081075503040001d44003070166140d0034008084e0012651401c142003806000720952144031442003072010103503805030707109000b168180ca40c40788845003031510703008405014044004840034141304264a0940300903400c0d02a00c400001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 152544235 1250 152542985 152542997
    0x1d060406060909020108070c0303020d091110020c06090f030f19051b090f070c1712010b090109120609080f1c0c1b110d050309010219030207051e040606 67
    0x1140ca400021210958031240540382003400082c05170f038000d041503600411034205441c000e07080e03140890091060990075400d103440c128820050040603540c031010842d003900c4101600e000c00d44243d0b41e403d8075a002c41e03800303c0d04001c0105a0304000c040c103c644200a02240c3e403070b07070841194900f48540ea005c0c001a032146200c1800600000300070902e07100041c8000c4c200344030200c101080103211300a0801c91401e204c4c0010030f0400d0b1041d20880c0415802000f50136155481400e80308017980091268043e5598160001c07501c1141d50084079101e003016142d4501c0145480da400710003881000040c0d942c107a5524404007c251940d004080e0313001c03002c0e611940d4520039980d10884484c071003410000180707001c0d00e14510680007007501480340c0c80803d06014050542c0b03803882c4c040300000348090300721000480200401c90004098185178000345c0070740c1c18544150003080309000c41d40300080d006a10808040003141400006080c0e184080321002901940d243c002c0340c25500958012400180c2d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 152545485 1250 152544235 152544241
    0xc1413050703021e0901142109060601020d21111201030510061401090b0906041a0c0606010c03020a060b1203070c05100e090a05070509030706090e1b1801031d06 71
    0x5420100c41100b04800302130241841c09410000f0440000c440388040b0840000400c0c40503442848140b0401c0d0580800303209883c50301003003603030b1103950542d01c02d07001d4490306032105641c9d40544c80d40f5015007000070340c40158cc509522201b0107000c803002d00380030358001001100420b02b0b9001c0350700c0c040e601850040c0000d441d903005000440d10941c0c01003018411541310014140c2e8442010412210328001481d180c400110004003d4882c1d64402e0040d2120305000030200d4917400080d12900c120b440986002d40d54203401900d030414010300c02030040e000b040003480012000d80c800302e5580000b82000030070f10b5039540810310f591310900003500e40c004002400c01981ca020041e9100203035251602c0c2c0440e1400c080859413580c406003208001d01d45420000c0d0301c40348a00c0a80303031080e5008080701d480369503c4502a2804005005541c2d02a4100f0000703081030840c0d03603040da00310300b0512031280780480c0746100d109407029403149103040603162501514100500307580480817411600c05800242 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 152546735 1250 152545485 152545507
    0x110903070e091203060f15090a0f080706410a02030c07061d01080a0b06040e0405060106030911040c02151618031205070f0204020f0703080f040c141305070302 70
    0xf4148040341030442d4204100295515418610500c0305400d44103201c40d401c001c1820070a5018030300c030a50b08142080750000d00da1030410701c194210b441c0303a1b00f5202aa40c1780c40c41101c200111045d43d26030b024040c8020310048000c1400d03d01e0160140490320316800112740d000040e50f00140003200141e001080c6400c56038000e0050328020101030510200002c10a408030b440c46107100b104505001003503001491150198001b40c074031070001041240d0b02c035100c4803005003485082c0c1d0151154071500c0008110f160091040c8000140c215405082403640f280c2080042c0c15030100350f108501610030020307442c40e880b1004c10700030710300a1032184d545030850200414403140800c01104030005c0f01c0e410004075001c03084140202d0b44524280d07943c1c2d0107608140220050340580203400503c00101003600303501e40d0b0041c00c25603201e50b0300c1740000d851754110b001042100351405080041384003001c02001d98031904c2c1c0200d85801400d800d036490300313407400382088500849a18002c00c1e00094100064 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 152547985 1250 152546735 152546743
    0x411060301030f0209070e03211b011e0b240903120309010c020a020d060209030708030403030207060806220509010b0a030f14030a050a08041e03020a02011209080d110903070e09 78
    0x40e80ca45003110545480009070744054802120109203801002520882240c004075181103840303074030ac3c06405010064242c000c0440b0042c0b00c81c401542141924400414020090102c0c001842c0348180600d190841503d0700b00c1c0000b18441e250100200c40003904e0034801c0390b600030300d10b021031030301e0f03180144410303095400e11171107007045411401402c4010b03a81d512040074915086580142c8405a86001c00d140012680000d8503511000c200002016030001e20301d4117644840c1ea40940c191503031028000180e0b5440013554034041c6091054508500039071086a00c290044004500026407901050001c0c0140c1c00070b44075a040101041c0601c04410498100745042000452401000c1740f03005015010301c040000400c030030003002c02e01340003140600300118558103000515440da10f10f40a56640507110080340441c047d0b1003d0300c5c1c0c08605109041d0b80320380050a8910303103408025000700510000000c42c000c10401d110f0300300541c40c2080f100e0042c202d403034640c03a60703420309102141c40c0c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 152549235 1250 152547985 152547991
    0x605090a03120309110a0b1c060f0e04050c04050103110d05030405040e070509010e06131509021206090a15030305070212062a1303030e130c0c060b030105040209010e0411060301030f0209 82
    0x59114403801c0001211000803102d03a81c07101041c24003800b4041230410050501c5d68025085644003c8021510a0300000c8044c000c80c03050301100c0104903000300f40003d4543c01d201c0680044051041c80d1813600340f000c0038040040c4603400303680ca46502d440c005003c4500f0051100016404100c0c284a1410502c40950160140c80801c84c01031604d24001201040240c114025003600c1b00c04501c0c0c0c000000d91040007405515009548401c502c0c898204900012101d4500c100048008a96410914811342441c0007640000b941150b04684040c3c450758007154040f070308528400094202283c0c140030040c01340724864070b09035401121500d44a4000300c41407844851040c00c020780354081320304603c0c2401b101d5140c10303c011040001c20004d680449142040c00c011414040711151040d403080052120f64407410082204010310403c3c5400c903003003101c4c02074100300c010b001480b440900300c01d050b503c070344034000303e0484d10103800100741d00b90400e0340111026400155614210b1409034810f0754 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 152550485 1250 152549235 152549239
    0x2030711030712020d050304031a0402241b0a0f061b110a110d0605100501181404090c0803072603060a030303021c0e0d020706080f010605090a0312030911 68
    0x40201e0400d0f005610100010790024070900d504034003c420064140152402140c00281900c500f80b01030001d802141c030101d404a11074031944001e0160116010b07034001e01c6811106501c2d0800c81404c904018030200c0340b00008062140c150b24800094441e200d8a07015482490081a400307070b601e445418003c807110700001030001190b9143d80e91000010701460b420b811240e41d1513401c00300302c0404d0030b0b142c010401525407414801000600d41c0102e881c007003201c1080c1ea50010381320500102ca500f000b8103002d002e40da001c4c0d00040d03602600d41038100d089020300481c0d5201140ba61401c2041c95580007a904460901081140007800040095043c0810146203030551840c6804400a450401180401024542e020a0410720000140521010454840b0080180c517035820116651071703480c429184014421110701141e454803c0482501880030030018000d84d9007814000d03103190f000403d100382c003c072640000001007031145141d003d00040396140000c46400718100301c1c40b03603040007110318 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 152551735 1250 152550485 152550493
    0x1201060f0b0c100504080d0e0c01080a0c0507110a0b18010206070f02030d1a06040303030902031006050a060e03100606050721020c061605120d180f03050310150203071103 75
    0x207101042c0411890800a4001000503441e40c0c0c6240250b014010039020b40c41091604c00940030340400010382001c00d1000762038282565452040401c1603541c0ea040304400944241304c294000703424080c1c4d09011450090a078046242c46902c03103140d5070050040c2452132181c543c5005903558040c0038054100003030380786c0f810407080c83c4400a540d0b441400810310700c25540e40302c0141d03c64022950f1046951008001030307525552410002c01500b41e2203000d0b03100303024001962a580c81c03140704140441d0b03801b03000b09450501d01b003001d81e108808101403503014003d86c241f6841007062445040042d0541d41c0701c2c0c540b981d0700341c2001100300800500c141d1201c080410300c1400c90350006942060304100301c3d51503565180082c080030007000c0b10580281980300d0218950756a100c0d4101a10405003406d1040180c0c0100c10b68020741d222141c140a800d85209a8420300132030300c00c10007560f00026038400c0c403a0741681d82342444c13107040314100014010380011400d4010441d02e400300c84120f4030114010 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 152552985 1250 152551735 152551747
    0x2010503010e0709080709020a08150f130f0615020d020a05060a0c020c040203280b100507022806030e06090c060a0c0602040f0e1311010f0309021201060f0b 69
    0x68958801801801d02e245820400941c0440c46003d100d005804071405440c006030b41d40c082d801c0650407820350300010074880301c000350901201c1c2c1c403009503a21000f0070401c0c0a0304d2800920101c6211002d040340e043c0d440300346502c071b0001c1d24051040202014183c184000d6012540203003450799440031141150010f00b001004100c0008100c1d400c81c540000c001044006203000ba8981807407208003071f03089030000c410800903910241c1c0d920b41c907840c40d801e032940c5014a4041282101c003845070550b41720402074007103000300e0720401c042c2c0442440a01440320505006001c6100b154074403400040202e1001070074070400d276060082c44000b0380c401006007801c0c00c00b40c00d040e4032800541219030084c540070904940b140d1054811900040c1c0044007103641c1c6440e0718140c903402d40c0071b00070303c0c01d1840c0072000b0400421604030340c0a489900119101564021800111090705905010380201922454803101580e5180c1982c8400c40400300005001031601e0b0440250540550103032a05110601003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 152554235 1250 152552985 152552987
    0x90a0203070c0b0c13090e01050907060203120c1b010605100201021213080f0408060106030c0903050a02040b1201020d020306030d08100909050114150f190b03040c08030304080a0f02030301030201 86
    0x20303402065600003101d60300c1c0c0d40c80344080440783c00740080ea900c010b042c098001511961a1f8442441c59030a00020321441c0da40b488140d87d1079140f4441e480041c1d0040190750721490041128540144c8403a00c21850084003050100c0030729104142041d0a96651320100858030348140c01c003070f5100070b900003541084a0030307000714021a070013403c0301c4845041ca80700c1c80401c55020111500703205101c2ca05a215502c88900c107035101c0c030901a20300880c3c9001511285c06010b5240300303048a074401e0027050200d0a40d800e0001405940b104550000802006080e0350082130018050014000c0d80060300c91900d60205450088010881d2050054820a22070080c0d2410024401c0d40c004000c0854446101d150803401003800142c840b00c42031400c02848020000741e5035440030740b0703804c40e4100c0c52001d0400c01c00020290340c40c400c0100c40c140110821844620780040e6a00a014410750740031035540ba840c150440c0d100326400c903000311000416580290300416280000c01c0148015420b542c15980 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 152555485 1250 152554235 152554247
    0x180a030c0e072c09040807050303040c030c0803180d050f030409090b01090b01090303110312010f2c1609080601030b010e01061407030309141c1b021f140403080702090a020307 77
    0x80f03150300540a40c000101403003654421100300755440001c07241e40c2e1406007012003024100e4001207508000c1150b002424074000801e45400052000c001c4a1581b59001003008104001e0b8084460707001e00b8485450890003400504010000d0744030205000a50f8900b1207031010050304281070991800c0100d000d1360341d103d00d4030360030359506003800c582c2900818029451802020204941606117a0020400d0240681400125041681183d40c81d01e07090701e40351072071081c00740c0840320515280006009408240301540c060041400c0054825843c0d140b8603041143c02d070030607100910f824004001500391142c43c00c0c0101a9860b2040e4418981140480c9a1080244c080c08050306c602d1081c0500c0340780305c1a4100c4c2c154403401c881c1c56070903400000d86903c86100c920701c0031030307907814600840c172854420b54914a940202000f1450321500c1e81b2443d281c01e000d0105041018000b00311043e800c8040040c0051400380c06081e486001a2042003500c0c40000d10038202c90340180103000a581d08030b6 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 152556735 1250 152555485 152555567
    0x71206030c2d150c17120c070506041211030c010506030f060f060d0819030b040c0f0e06032703072d060b0f0402070c0905010b04050303180a030c0e07 66
    0x100c0103031082e90712441180d4420b0007690203002850725007803440c0c02400c840300600360406c5881c000d11141c1d44120000307071035024100c03001c0d180d508030300700040c00a0404408080080b00c40e0400300c4508007202c42d03461542e0031001e8008480ea543c1c2c41400f040740b41c06c001c198403040c05d00c0c0003000380d86411408508a01c1c006400313039001d61312209442080117004415140320f0808041c1030052007010b1100180501071900c2d40354021031400c407400030134034494400c15244460580f10b038183d42c0c81d84406e004081d07100a0000c4c10205071081c0304103003030014031440100c04040d4401180c40e14814181000010040b200d400391120702200600b001c085400c80c0440c000b60841c200140e6004050b01013401a112014416800742c80000c98904101d0300320300180503950308120810590380c80714450720b07082c8603a00400c3e40c90790052100444141c40f56210f0180142d0140c0a140c04540da5030f20100d4080b029000245104010300800144e91b6003c02d50801c0c4080002101d9541c070520b801a0040d20600 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 152557985 1250 152556735 152556749
    0x150b0301031208070203190c060b09060607030e04020d1b0807021c050c0c0a0f03140607140705070b0d0606030b01230a0201180506070801080d0215071206030c2d 71
    0x107900281c5145e00902c182c1c2e05003468a8080d09104030400e00081100c0e0400f4403c484d200c0c0f0b01000711032142019200144143d2001d440c2c40e1404000e074409658072a00540c0c9260700507003c0000854a02c5a0300403020703403030030b90409001c410310080d00180400f02c0043c030b020115032200321a012003240c1101d0402c54411a030030701c2580e446086414500708420240840d0704a01040c800181c01078481081c2c00c2203030b0003003156124103a1120041038036040140c0e0001d000984407107441600120000085c0b0125210b00100d8604641c0c8100910842c1c0281540040e0fa5586d00c104004a6401d40500d1884110910b4a2a1003480b0020303584800c1d00204c403540e80703200000c01d61680040c000d620101d5403407030700c9240310442e0080d4500282d03a0041120880300090000c400080c652000158028070f02a49401604200c0f5507050610b500d0540144884100560f10f04410060ba100d44502d00240d4003034060001058245079001c00c08203041c061007058086480d031003440520340c3d41d00c10001d83d100 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 152559235 1250 152557985 152557997
    0x405060712090506070f0f09050a0e06030a12030b09060f0307230d0807050f0303010f0308090a1d04020a051002100c0e130203010312031a12120a0201150b03010312 72
    0xa100d07601d1000b401d00c410020501e00c0760005200320745400c0707040e0014452485d0344500b020500c2c0e9000710346c0c882d454414503030411401481480840e030ba410b000c41d03100354044e0807103440f0609a00c0700342a0440300314803000403a0b03441d82c03d1030007170802d500c00c654821425a01c1181c04000302e80825681d104a20802c01810341c8001d07030301c941c1e40c500b107403042031200020484031400740e640c2410a9140e02c580e0084829203d4060820030301300c00030081da81220303030f015418140245191a01000c0d40c0c03101e403031307294814000440440c40b0310940700c10203201c8200300748540803071500d44103101c81401c4d00d1700b10074480d01c0071a40d1a45180d034002000790020000340000f281400b020242030340c413091000052644012015100140304260380d0156040300e0013480080c8802e810820207504550a00c61b04031030f014540c1c41c48da682d0341403905070105480c000c08102e5181c460050703202c10303082e041a032070200141d4655086129a0070f1914451000d000200304992641d455540c0f2000b400701d00503001018021 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 152560485 1250 152559235 152559257
    0xb072003070617010f120611090406090e01050708150f041d0a030305070503010b19090b040b0a030b12190c05030a1113090209130c0302030a080a0f050304050607 71
    0x95042502021584080c0031501942d49511010304640c40c80e0034403860801203440001210032400c9000d1007202c00a2084a00d408096180c090107032500034031480b260b00d001c0020800c151590b00c940402072069103c002440c0540d01c6020342542c1c0701603c80c4040003141028001c8051101c400d4036280c0404403180c10100d20200c1c0030401908080044c2981074045500c00c44c240c11020451080040c0300c2e43e0100309607076076080306660600023801404480081400000c440c940c5a20b0781001801d510b0402c1c0e00525035456150703000b940135401c282403004002c0380f030000c000e4060050001c0c0c100221901003441c0f100c0d000c1a5543d5002150200e00300100c1c034039403418031501d0513080015000c06001d4420a00a07400c041d04c50300150301040e40901580060008051101c1c411401c04030f5005000101503225191103030280b0515501c00c0da018100513800000580d0100580400107228003d415118680c0002c003904d01480030340e0742014407100300100b100050020981543c000844e0504145002d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 152561735 1250 152560485 152560523
    0xc0d0b0a08010203070f0807110705010c06023c04210201110f061e090a030f021006170607050f0409020d180b011401092601020c0703080909010f0b07 66
    0x4031095000e180554030000920051903842011500390020588070030600e621054801c403042481510010720300c1c1c010800912680d0300c1110740b082d855004140142c02c1c1901c100714405826050612020300e0070308507000d5081982335104c040d03a000074040003a802e0500d00402c0030b90781e060010720100079207112901c1c80304680c0543e00d400e034070303161003400c54000b0740034a418a596520140c6404034601600c0940d05181d00c10065218403421011026007140d1805903400d85580201314a460158014480c2150a56004c0d1090400134120340780c1d001c071410614003c40d414031074054442030802c0810001e02c4040c189440440d800c94814840c0103030359000c0da9040400502e51003242d450035150303421b240d60512081400f10f40c161803411035202d04040c0000d00554080c41d4500ca03400c580c1c0c250046000c110308001703c038021009070380c0001603e4251402c2182d03080c0100c9400403106220045031000c9907080107983c0034050700724001da913511a07042000c00c0e0014004c0c40801403100d103200c0800f2070a0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 152562985 1250 152561735 152561749
    0x90c060d0e15010f031a04021f03110f0301030606060305010b04060804230105060103141324050c19050423040e061302040b0f0a03080d0213170c03060c0d0b 69
    0x810b100c1c05441543d5031101c0071400340b4413041c030051701c1280c0303600965105403401c12683c90007036600826919060003464400450400d906036110149661030316142e0703403012001e00a202000039556090365940c190b2801c94101c0e4181d81044040515180040c0100c420b81c0040f501522050306003c000d50f6541d207002c40c80c0741c151044500742131406591120b010081500158000c0500b40c9081c03003280601d0002a800070402c50b010001400e0072150b07070005c034100c001e090700703420103200000306203500c002071400c20303150300341d60030550203030009141011110030841d004086042490300c42e00d01880e00e902c00c0f00c00c020b40c42000440212920400466070340d036a11449071540020140d0700e403444c05440500140080104c140d001d07a050403030500c80e9150413414080c01c0c49005043c01100c038250307111030340e1a401039201c3c40140344d401c01203050700c0c0c00740420440003804524120610503c00064550401c0d4101c04a42d00039072042c018811790540e18025102200c2074071000080f5058460f001840b4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 152564235 1250 152562985 152563003
    0xa061202040b0703030209010e0301090201050f070c03050a0c050307061103070b0a0902130e10020f0a0e1201050a090c08151b040b03040606210b0a02031003021009030506090c060d0e 80
    0x2009400141030f80415030180c001c0e0104040c03d8941c9000700760500141400c0ea04002d80c020300040f020829003c5021092004d02140c034014680880495120380e9014500103080e03105a90f00303601200c3c10400b900d403c04c089000b611151034000030303040d000c1c0c013210360f41c0c02410002002d0840c018002030524056900503903d0980080c450341c1c01c4600714089030014044224207086c54011b19564a100d42244d0080b50b05040411400b1890705104440446180f02900d540d01d5103e03002d071118601c035220900a240c05402e92550014182070103150100300919607501440d41c40d04001640d0840c810000304050b840880850010b03d031420f10040003d6501c05d58000c1040404040148020302c50303264800c40c2540d03440704240d40c001030845109009a10301140c01400c0402030400140c07000c1a9030080c6800595a8004100d16a12039000480212560020b500042c1a0600400a00c541000101d4219601c403003d042e80e01601c1c1c000c20000d108a00c12215150b4072080341c0f00182104000040d1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 152565485 1250 152564235 152564249
    0x3030e0a0605070f050a02030d1a0d06060e0f090d0305040312090b06240d020a1e03051b190c0206040f0e15090609070e130c030207060510050a06120204 67
    0x40c5510461410380010076090300c1000000f602d40c0701ea6040d107400b440c210740712010550015400c0070f0f07210300c260025105005691f00d4040050b4003840c603c0d01c81000700148103100e0100451400e0032300100108804006008a0407000740c9000c0c001a07010105803150f050b10703545030206035992141820740310080c2032500446400d01d02894003040c000503440311400b45a0856002c0030030603039031080c3c806c9283c500854003407995003000a1002540103074000d10240900e42071084180d00c2e0b40050f5103108805c41401d20100391503c00f045100c8269440180c055a03407136045504041c0c040384d1010161110f054040e00f400101441f42d415552440c055400030f1141040d5200a04c3d01c030100b0321501d0030140c400c2c1d10648260442980d83d45485002c0728441c16000d006c1c512259603401081311015005021103400151180c0c0c0c011401100380107200c01c4101c42e031009641c6290f1442e01c5c0c0103c0d0340040410404210360102406a50340b9081144215400c0d46005000032115041020082c411507006031 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 152566735 1250 152565485 152565493
    0x218120c1f09080703020603071d040f0c081b030a0b030a081b070905010303021c050c0604050304050a090e0d0509030f0a0f060f1e0e0309090a0501150f0e0d03030e 72
    0x440300707007200c20110810740c080d6039070341c4901940c0b103540c10342d19002400003d5124a081c000601882d00c11508030310071403846d20b29856a06409404901129468015441125160016041c3c2c503500081d000780c00c14660440c28000e0404080c01203810b020117000c41c03010741e84a2040280c155400c100c0c0402c2c064100050a030f81e1604640c0907107003644002082c000354010440e00064040b401d00c00c2c14103c0c0e82580152000b441403e460030107960070b81c0c92480c2803000500800c9040c000410410303100b244104021603580e410001080710701019944144010380c02c082e4440d41e03200f0081810301c0c0e00307401810000e484804010020b41004c00c60240c00000f40301c1c0310f0403c0300340320f200d40b40400020300810040000014000303d8038103440380104000c801b10342440c20700d0400007265114840f0840224261fa0404402900044401c00700f5221408107d40350070043c44038280b059205810300c90142000b500c0f41c20010400740800c816092018031484062100f501494001c1d044a0a810325013016a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 152567985 1250 152566735 152566759
    0xd060203060607080318061b041e030506090705010e03371505041a060117090f102c0d05030a0603080a030e06090c1c150501030309180218120c 63
    0x80451304075183c0d400140300d00c4011446004402c023400d10507088207001d01d8545401c0c61813040122010000e542c0400d006202d0000110b0401c0c4001401a0380d00d5000d45071075131030440018400d86c54182c0780c921940100412059641891701c00b03421408002c3c3c0682c0703130004804404070701104443e6000d4008048142d00382c840b00f419500c403070310a902c2070341c601a5111480540d100c00301803c407840e40c00301d0700d0704220084008094108540c084041c0e0211200c55100300111810500c1c1480031510391030310b034511821158815400101d02c20a0222816034080800e54842c1d40e994045100d00148440000443c0090303540d034101001554224110541c0d481e00c03000000c00524000d01100c140303002c2c0740c012800c05600814070924070040140b501039400c031000704003a07107418000d200301c1d62050120903160102c5007500071540294026140e0904d610b00d4507000303900114611001c1c0420600c10072040001c091b5071001c070044140c054818a014035a00340036140750100040107198400d03509107074 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 152569235 1250 152567985 152568001
    0x31802120d120218012102041203270e0a020d0903080114120714030f011505010206010905010e070c02030a0615081212070c05070e010b12090c0d0602030606070803 72
    0x84402200c0540d1440c00749424150701c0c100b00e008280b04861035007622502d8082c15031180704a1408844000d0b1903856030503c14406d4000c0780e21941c0310404840c50120040180360b00700000091138040180855010300b10811580001c045c103014821000080341c021408408140d41921030400100d0001c0224130100e050181c000c100903c0f5202080310410204d49040c101400c034925141240740c01803520380d08103154050018600354146816106460045050388024000c10280c1c50a1b000c0302150282404002814490142c201802590030b1070010041c082c0c102e220194031298526100100710214400217007010440800906400d00306181d801d074201c548003007070302200e003000b00700c038460202182ca086160140095030795680144d81c0028055600900d072500c442d5100e00c1c1900d0050703465180030005070400380c100c141900c5010031301008a14030301d221140c112404000600c01d40740048001112030740303000802000f0340e40210208001d5212034080da1400e0394000900b540303901d41100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 152570485 1250 152569235 152569243
    0x1f0305010509070f05030109030f080717010b0301031101080412140f180f010306060c02040e070f08010e06060f091603063b040b040b04030207170a0201030605061903180212 76
    0x49802c611101d16002551b0f00e414800c811101380c1c035031036082280064140543e8202070041003402480246182802d4031701c0e460808501a0920503011900c80d41036003042e080203049240014140704003c014071004c6071342e0780395100c81e048203440c2c8140610300da460000c655000d10100032010302404a6407200d01406410700b01103444054a46c0c05001d01c5801c01103007a0303aa2031141c00003058420101c00058103107134010001c010494803c40f03a00c03985c0c1d00300684040700d080d0301014013a5036494030008071040030f100407904041c080350300846c03001c02c0328001035860501070034003590000200f00c0c00c0e0215010b40c00c00401004861001c5215449000b00a1a1144425034024440501800030742c038445040800030701841d00080001c04a42e42c0390741e081d02c0c40001500607010740c4581c4100192521420400d203002e0386404024103515509407001405492141d0001840b0701402e001050700540030449a02c80102149004074000c00c2005d551981074071408000307500b0140710810b910011500003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 152571735 1250 152570485 152570489
    0x40504050f0c010212090603040503070b010315180b010b031e0903040e010906060e06130302040c0c1211030921030a1808060603070b033301030b0411031f030501050907 74
    0x401d449101c0d02c1c2c0001240c0750504420840b1a424082c40800d12604050029591041c410b4049a240c4542e5840320002004240d20498207400c40d0821180ba901b10740c000c8800e00c0500e12081e00d0f000d4803070760700c4551081c1c050040b045418000b0000032007079114052500006481c2c54021030311818041c4240f5100d40c003a000e4010207052200001414150314891103003112001d42c0c0d010190000d1200b089140d601c8004e40d8000b10000103130100140e900c03445000e00c0ba200c55200c0710059502c034034080e02d070804840e9402042c8924101c44202001d400b04c101c079900710b801c03910303010290303180d14030701c01b4070b042030500c1d520030340f01c040b80715102540c10081010302c4801c40c052100c000c55031034107502d950304002c8a02d81d800d030f041408200459219400a1504402c0542100c601e8940c1802c09491840b180685d00c01d0640e021505203410b0f50b094429084d01880a80d010300480d414030558544512000c0c141041e0274813100246092545581c1d01440a590321400a0000703013089881c15a88907918 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 152572985 1250 152571735 152571763
    0x302070504112107020f030d0c030e0f0705011101020c0312040221031e09090a090b0c09090c0a022a01020105011d070807030209060c030304060f0905100504030c0204050405 76
    0x1810088249680c0c1030b950503101000b050748030070100743c2215068040c0038003030806620500c40321400e060414805440c1004100c0e4001032103039440300d0000c06480a00c155040c1c180c01482e43c2e880c480c880401d1007000d40781c080c28000e08c840740070022a0b009118a0003c903019000c08a00d0006c3c1c40c44000c41c1a0040340200c4040b0b482d0ba200410b042107485010b20723117680d613230b02c04c001f4888214031540000c1019410154402d0070511210042050034004076000c10440ba50b908a01040060400702e0f08c1d04003000c108418200700098003c1050040e003e0990408040f000c01c400071654800c22041c80c804006040171400314610f80400038198003c172f034860307000d9400c180010a000e450032000d907a030b29290400120700b586428005490541700139201c801055000c01c000a600e0700d4042c010322030401d114005640c1c0c1c2c030305403e00c2022114a18560207806040401100c081540042c000141009058001546844034581580c3c5009100c0c03000307400c43c1c2440300f04010300c1804241340441c1405 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 152574235 1250 152572985 152572991
    0x2060406060504020a0203030f040227100b04050102122206170f04031d040b060c07090e060c040b0f070b1014040b01023003040c0528032d0302070504 66
    0x141c2c402c01060740111074800005900900024441c4000541020707085400600100a00120340300d4072640c1d9460f041409002c03000c2e000070720540010901e100e400511400c0e048906040c20030300000c1d00d0b00706901d0f22407590072010450440101c2d6045004501d000310032130285029958500203062070200080200400d82d81c0b000141d541622880d40324852076060303035505101030800300d0b4421400083d90025402035038030920700040e5141d403402445560446802001c2440c40c001c03488080e00c4031b414107003540350400c0c02440f44860050090b60300b0b43e14000d541c282c50301d030441014201c6000343c00700030307010a004c1428006140c5241e00c5900c182c2d0403944104844619910500c020f0b10500c485950041e440002c03ca90340110008040c41c42c440404144001c0100e5100001d00f43e070410785055407560000e42040103585003040c28080c41d030610107c40e01c0303c080300221a4056a44e1880f002d4140101d0b480610800620a03c108118140c54103400f580c07141c15040095a624880c00740c18010b0385 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 152575485 1250 152574235 152574239
    0xc020118030f0201030203041104060806090c040905060105220c0504060f0507151e02070812011e03031b14010f050c0405030c0607020102010207050607030e160b160219060206040606 80
    0x451420025030b50003410304440c950701940114000e41c40100244c1e08205070344418107042e0340307034060603005001e032100524150800008190a1054920046103e0352504025000007800031480e41e044031411103498a4810317010034401d03810754400c084058074610780307561040c529403c140a0030541d01140da4961401440308810341e00c0740720b0035030050300c6034000001c04144002c064100040044000041180d0054408000e00603600240c00488094002045810a201300c0c420400c2c0100f01c43c912444110364040100070074400c41e400050100581c034000320060b02c2010030020001a03000540081c880c0d000d00d9200e000380310003d00301040500f03200205502002401c299401e56400402600d001d1085400f000b1940d0b004803c224195502444103101080043c40581e1040085817004505101d002c491941841c12403c41408018840307501403113001d0002040da4108002c819110b0400c10440c0005511546540d44101008481040200c0e440c0e50110743d40e80514428103042c00f84903 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 152576735 1250 152575485 152575517
    0xa120302031309020903060402121c0504030615051509030a0c060305041401110d020702030c09100312020303070906080403090f08010e1b0d0206180d0b091009020a0b0702010216060c0201 82
    0x3220740202560f05510440200d2301620b0507400c2c11134039981d814229100040d40c0c0c80300c0040e2018400e450f501140d07022804006100b0b003070213041002c60a1041402e4418100800101030104501c502e01e003c02010032485400c0e2020007080020b1038200318002880d65903014001d02401e400c4800720307800802e041400e0150113050054a12203420400c0740c5003002d10000d203040007900f2500050341e0501c90a80c02580a031104101c06000c0c441414901040d14110b04013000000039010344101154420000c0040f5154080821f406440e2680f4101c10243c9650a041320030500e9078024503840c40c991140055003c105501c82c1e941174003010241d981c80544520300b200c1c002c800840f903940008010400c24010301c0d040005101602c8900c40c0401012100401f0078803004201408803240a100c42c14040405000c0103070701554419140280842c03040c51f0301250069501d07104181004201103030401c11a0300a100a006111030702c0c80864406607a041c004041c124448409c1c0c1c0416140c9403256400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 152577985 1250 152576735 152576737
    0xd020604020105090111100c0225060507080d020702101d03060405060c0c10110304061d0d0e030109080d05070906080412050928060306050307080712020a12030203130902 75
    0x6950161a60f9051074030600042d1103103080f600d0b1500043c000c8120141c030704140d61056080e640c1c8660300034a1449583d9483c1089d0352260000030b0302000360128200000c039400011a5480e07640f100d07405460f007400300545c40281c0105038000754442c03401c40c202d10006034001110140500c101508200580e146020b15803904410b9501804a80101c00042c1400c81c0b45c8000f81658000f603400ca4012000c10b28074801120340c0341c420321200200c00014030060010600910009400a203000b100d00d144000106545190006101003404ad003900300c00703034540e0290710070743c0915001100d503a03071400c10a40c40c600400c81100e44030041890500045121485600f042d403149a211441c440e0201c4420350275981034200d03114190344055480300c4040c000044418800748480c440e98202d40c01800c000c0090190303069a00010f00a6001000400c03400400103001000c44894402940040d005400881c8540c8a0341e0840a6080d92010510b410594000000d000903640c01700325034501034a40d0507403010b07 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 152579235 1250 152577985 152577991
    0xf06050603191a0907080a1209091e0504021c0f021017041b050607260c030706020f04030b070c0b060405070e0603060102010906060b07060f0203090303012c15030d0206 74
    0x2000e001a10240002070a0b1582036410500300c40417207a40e0742d610600c0c1417070082c80312000c0311900c4860607441d0660b5006074140014100c842c00601001400030360850000000c0c0c40d401c0c194544840c041400c0d512064440340c1180c403140d0b1600c0d00c0c0000c60816066180225500308d003d071508000703144038184940740300c44110104040031602ca489580b215000190f03041100640790404070f20005050391800000d0040ca03110780d5010f40011507420300c035510640003603482820341804001100c6c0c1140c02100b00c4280c00c1e0b10801c016280c0c0300c409114102400b603500020301c031800040034050b21365040035061446600c6151210040d9450100f40000e030380d0203480900108200b00e015608515000020359401081880001008402038880406542c900d6110701000d00000502e20144550b50040d0303841032011365020740c61410031007400ba91740c2c4014842c800405210b01101e01e40680c1c0020400306009000500500c142480f1980101541101d00c2e140c0c40391040300940900c07940080341c4c1c85d01c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 152580485 1250 152579235 152579243
    0x40e0d08130b1315110408070509040317090f1006030506151f03060f03032102090603010b03060402090a0e0601110105040503030609070207081015080d0f030e01060f1203030c0203180d08070f0605060319 89
    0x28643c0c44241618200080250043b200790065010f94800c06e4010022003100114150380800c02c0c901d1030502a041c008040c00f8400800e450b19218800c0b615050400002144030005910f00124040d404030700030302c1142c01c640707030000c181c510000c00c0c1a4003c003107110705180001e010f04541c0c0b95081c818100e101c0c49040c41d40103074081c001004401c507400c01a580c4881e024001500d80901c0e4400603484180942007400d81c1c1c03040c00240b10386540d00501c40c0d46043c00c00402001a402c280d15000d07a03e000042c041e904c164924000686014424060390009003060422198681c04051001000d48800b0320500d29810b5030a40010701c00b2400210076140030450740f074081c0311680c108030850103401240360810180d900d80c4400a05558030001d01030080801c01c2d01b1a948146c10b1030f00178151071840a10408640c4140858030001c2d0850500703c620510440d0400900002850010030901601002600040b802c0304001b081c04000c1d00b101c2c0c070915041b020b68101840c80d06102103d819113140240c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 152581735 1250 152580485 152580497
    0x5120a0914040b04050a05010801050c0f07110d050304030311010b010e0906100905150705010b12060115180b090a0503060118050a060302040e0d08130b13151104080705090403 77
    0x18039207414040c40d5280015101142440031034011030300340e8070309031407003202c4542c0c0b000100036200080c49226005801030f90824903140d10041400c0950051503005002c140207079040800940c0c84c1e03d2001e41c0316a000c1e040c1e0b52680d030342c0e00340507103400b00c5584a40499420040d0030010b9600c00c550b0300c41150401003d402c041e8650f681031103001a02e8480340414002500300208076641c03020108401454102000d0365511040c5c41d105080d02c001542050007100284203600d402032020800a0642c0c079403c18110340b565901c0402c48001c1a4481c98041000f6201c9002c42e40b9084800145800300c8241e880015199840c014950707035000921130549a8200420024100748040d0030554006451450114449440b1b800140c102c5043c52205282c9520401c00745001e260402d520550140d0f414070740402480050725003030200c038001082001e124003000041c408001511031080161400d464040040c0c1c2d003601e8070b04400e54068020703030220b8030031414001070074074213044000d1003690701d56602 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 152582985 1250 152581735 152581739
    0x220602150112110301112205040b0a17190623090325060c0207031e11010507081204030e01030608161e0b0d05010f081c110109020d0f05120a09 63
    0x3e407500c0300614100ba415500c5521180400010201030109004510204581072004154002c07610002e0307070105003d541801481001ca950303018400d011210b01030503105412140c0380006080181c40c4008a04100103c2e42a100380240755102e8030b80c030600007644d403003d40d80d5038140c00f1000800300c8602940f64020071400d440c000305191548000081e1541c030855040e210359a04054074640c0f4620001030384120f00803c1400311024000c042c071100441e94410701c08258030340034594600512801d040c010005100000c04c443c0100f02c030310764076a90341580c20381c0c00d003807500602c504010040796001a0520380085480c83c80810503025003006070720070207000c52410072000000348601da11151102c1c01c44a0003e89181c0030401040700e180c142030001001d60600031000000c002c1c41d0000c5555502c0700040f54a14084158134032000c0002d4144450b0180710408228098a0011002500441403040074000c2105814983d5201c9100d00140c466030a60503489508c0c6008010054000400d20801 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 152584235 1250 152582985 152582993
    0x114031e070b040801020c0c060715150e070306030308090c09041b03050708010603020a14180405031c0912030c091206020f04120201090905060607021302220602150112 74
    0x118408103000095501c032aa03500e0404003207402c29404403070565000512081c41030700602c07850f098a0701c119016401d00803942c071034507603880f6542d080c0140c0580c0c680c540c2400c29054580c04d4001d118140f0401c1e09882c0808009020b405076210072004104c0d407101044c281c0c03101041c0000b0248018180860036a00d544800380c408414003001204008074250120110700107000c000e014140260020030042d28510600c0900e0141740c1c00301952030f100c525282d0140d41c440500300c0407180c40c520103201d0f07603c442c10071505610900540a1889150810620320940d00b0381081c09411b00444a0341c403103840040065054071842410000090304e401002c1c410080c040303d1540069005007001828402000c00e280c41a9100340c01c003056001c0d08800303040131581d200d10968040c188004050242d4100076001c110f9a015094000384a81510f0802c2d0400c41c0e13540e4190344d01200c004111b01e180741c40c40141c10000c4540c43c044da10047c0203c62a426104a02c1030103e412502c011054144818042d15 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 152585485 1250 152584235 152584273
    0xc0906230d0b0901060206011802030f0c03040311030a02010605090a060f03120323090607030605060d021c02040b03090f0c1008130b1906060e130b01050d0603080301030b011403 78
    0x5079007901c0c1d40d82c40100d1002038403222925400781215800500c081c0d4140044000862042030300c1d081014010401c002d0283c04500c0da03260403940310650243c8a44841c83c0a5805005010741606180300108041f100e042d415000700c4119802070321010000e4883c00307254401d0300d00b18020742e03001e0400c242d400c100044c2c1028501c500040780c0d1070001000c0b80c405444803800d4024803008101100294203024443c0c90130300500360003040c1ca040400038149060040b40050003480801000c180d0301160f044d49034040610003940c600c01c14001190396030349415040019400649411480c0d11031030705058040c40c0c00248505074103900070102c0b2036251003000704480b850300003400303680b0720030b5608074be100001c14424036a40645000c42136032464020641d00102141c0b00c0b50301c204204110002c0c820070076200c4400512204207021000304400c1141c038010303140f0b80f240c241d0381000c283c545a070002c2802080c0b03000d18184c2c1d1203282ca100c80c036682c882818a4031341d140011150f050300108010361aa01600d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 152586735 1250 152585485 152585497
    0xc25050a0b0a080c0c070b09041a22230a140708060609060702120a02040b04140115020304170c030c1017060a050d050705031c140a020118060c090623 66
    0x74031444d2100c5c4550071400c05640d43d01409003003001042100c1140b8140c09240c29810f00c1d0b03840c800e18042640e0001b00b0703070211443c946d0309c81405070980b052014107607000068103c0c2005005008803118400c0507801141c2180e2107070b0690716215502480801c0001068015603180d0b58541003170300e13280c0400c0142d6100c1d42c507190f48204100040c4005845900190015108031006403521a64900510080d143d4910002e440b079807078140744486241c8500246810340f1041249080c1c0081201c2c4d00b40e2a502c0365802601185c0b1420502482c14000001c6003106002d068042e5400c00360740d2410300440da40100d80030408220140c0413943c5800c0d81c8000c443e07000100500c1700c0703802d503600c42c00b00b0107642c0c40a500340d070281c020400c24821424200061103428203003200211401080341d8004000d0b1480105200d4200c0c400101800b000e4400d401900300c0c003440c00c54035100010b040c0f610344024401c0100c378002107500300368001101c034000e50440340342200312144885411500d2140440c40d40c001c0c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 152587985 1250 152586735 152586751
    0x1d030a030f0e0a17010207020111060903070f0510180c1509090c020a060c050702030105060d1703040318150806090105210304030c030507050a0803030403020307030e03030c25050a0b0a08 82
    0xf0360b0000850704642c008406006840c20001a139521040c0001850050018007030001c5074804007d02c4076080001045840482e0080025148440103103001070802c0740c0b0081820219041c008805c14007240d0300c21403410b891084000b110b61513034400081155030300d042111800301d8441403040242032004e802c4140781a600d481940d801c0c205a6503100d00f25001c06080c5070004002007111070860a007441280d810010480322240000540d40d55074007143c1000ea00e45079010008030100e0100760181c42504d8000c0070f200d40d2072144540300d03138111640303010030f180d1400021102004a845402c0c00b481030341c140c89010b0400d800d07d03c0c1508402d078041124480c103404502c400c200000200b90600849005544100050702c440c500c2c01d800c02084c4060344d08003884582041052000280d0000304072008281c0c0b41c1003c010898031800080c0c21405400350f01e00450003510f400d4117480b0417044a034252041d818801c806069260424016203900342d0060f40e007008000c0001081903400751028030351010030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 152589235 1250 152587985 152587999
    0x610020109120302180d201203070803060406050f030a061e0207120f0504061e030b040212060a060903150213080a03120f0b0f1002030f0a1d030a030f0e 67
    0x2450703031807140045241c201030002907030105510b500c2010003000f1040d180c0c5c080701ea440080c220b9032540d0b81040c04c0c0d4402c2d00400044c040c00c00e15140c0311141c46105411074507040d2921a440750629070302a07801215410720880c0f82c02da0210705458040d130007005400c00a002800782c0c0045940c2c2c04000c04400c1c20014640744040c40c1c2d0b2a0008080c002450340d1032041e2105081303000b00d110081c16030444007045105110302032006002c0c060740b0008003070b500d4483c04050407002c0c050040542c0104112100c150304240000341060000b036000704514001c060656401005954404048558401e6400020180007c4488006c980e0103a038014200b4114007650a621a954400005103001141e49080703010840c0240c040b510020381d403051603030b6040078500500001c2e20345d50024480c1041c64060038480c42c41c003142c80000c14801c1040d65000c1c031030745a18603a9240c01da9070103460310010441640340580003446900d110304008c92409125541a156139000401c4000706481c4200c41902c26078100c0c40c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 152590485 1250 152589235 152589251
    0x5041a040f020d0c09182f120408030405060f130803040218090a051902060702010522090f0e0a05031b0c0307030b010602010507090807140402040e070509011d030606100201 76
    0x141c3e00c100745184007aa191980e03858602040c9003002c004001c0d140c0d00b5545440f41f55003a0031003900002c4078020441d030302049192046034400c00075004503003461042000b41d404200c204415400290f002d503024100b1a2103691321543c40c141c0820f821607c0710142030080310104000b88100000e5600903100401281c0d1000c0703400945200010304640e803c90541c440c41851080c484240000c0e00b16200324500640506403540200d8400c4c4202c060080c100b040c0025480c00840b8280c41d415982040203d100b01812f40c0c4074028009041030304608956540340240010031038400041c8031071070550080c095410035404040350a11240381c0078010070350340100000840583d80512180700958031031010342246504000c002800c551008180d401404083c0c14144001d4400046440c102d5903140443c10348580c840380483c001c4c0c022540a80d0000e03150400340080703140c100c0b005c0e0801e03401c02c0c0d8501c001a50440b042400c118140f0440c00c1e010340060303012522600300b444c10b40809940600020603042 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 152591735 1250 152590485 152590507
    0x5060c011404051e0708031e090909240f0c130305010c0306030b0105030606031509030405031209091b0301060e040902090901060303080702070b030c0304050718050f0105041a040f02 80
    0x2103002c44044038150041d2800390400101d19020031548403020005000107070a10122030754078452503001c200c0c5004503c00311074013008900202c0d100309801420041a0307080264145035669294003034002c2031040e1a80210444a046640521a11501340c0001c92901c990310900440d51000c03a00d280c610701c0419010001c144240503100031214181c1d0002030300c038603504100480c4e00040c5c11592003a00084107118142d6000100c0540d5441061040c0c0c0032030711100310710b500c0c5104550019805010b50585454a5684c0f40013400090600f0744070840650756840c0c2104542c129440300740d8403500180014851035100d45007a4400c0003000c0d00000340c030092500051020101114100c505a440b11000d204150340000f40c0741c0c121519000078860f05042041d81d20030ba0000400306030402101100003018494200030040080070042e40c45c0c20440e1982400b0f10150604503004880e06042500000b900e08051149a00c6141d81c88415000d01c12034070704001c0508454442040c50395028401400b0302 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 152592985 1250 152591735 152591771
    0x905010908030c0315010e0105121f0815220308040201120617010b01030b030d03090c0b0a080a0510060c0320031b060c0a0e13090503030c0c160f05060c01 68
    0x35880b0040a00e1300c81c940840f031941117814601746541040b00700016401d460341c204064680750706001510141554560001d803000034081d020081500c42c00c1d07280000c442d280864620b608903804620144030399a400b0703a03100582041c00c00e40e40c042c600000c612010910070a0030315003181c4149001c0c8062480045041e0a86030b8541003502001811412030b04400350034420f00f04400c400782018400704920707400007515400d50501200074507485040300410041c04903000e102030300a1072105510f504030300400515451080752058141450400401c040794581c801d8441110394942d14000c00c0700a640d0b04541c04002030b000052000c1c14031030410055202800502052520f4150303500b003121401c40c1c25840c1030030150510a01c3c14042128040295024218600c449010349000540108118040b00148911400907240b8000407052050440ca0900107044c003075641d90840e481c650034a04d02d40350b1400144204518039400e814204000d00f4408045d01282c201c1038000191134100300d40300e0300780c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 152594235 1250 152592985 152592991
    0x512070504051f020d0206040804120507030602120103020316081218030a05251809030507120c03080105031b10030e07080717060c0406180302030d020703020301110f0409090501090803 81
    0x1403c504108400f295644c100802241414075100030005130615484160704c0d17209601545400305003c49030070090007403c0050070021030703014804550300c0450a00e40440214207000480c481d000e022a504203028440244405458000000d44180504804115505c1d8803601d04007880900c0059840780d15030b014170548440368042c0b0090203500c125840c011000b1402954047c409600980c800c0c800309101800c01400b08850080004484803242404c1d01c00b07001d070401c014103810750881101901c640c0090b6004103107100707403900760050741c171881015101c0d6001c903d805203039542c8041080551401a40c0f10203201e816040009602c0750520301c00782010400d810100d070307030f5100010802801109803458611090084080d0403d400c2002ca00d9020b841940308241c20401c6010301075840082e550352590003035038020b0440f400b00d0490301001c1d440720914442688654a0945c0104d85816030000f150440d16440340b0491802d82002e4042000f0800c09000743e500d0765a400420000403400002940 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 152595485 1250 152594235 152594269
    0xd0309030306090908091306050603040804030519030f0e1203130509010501030e060411040f0203070206190b030c15120c070c05011b020607051005070e04060e07051207050405 77
    0x5000082400d001e0240e40441e80040e81c01c134503202e404008280c2c4003003903804022085401c01154481504841e001d000c290700f0565109800100f4041003085d541d0003401280d210303c05507a251007880c074206100e25545c000180200710200b807443d50a40c41020009401c1d08010550055440d00c0500c181c5990003811200c07000f800490018443c502d884001180100000d18017805800410328046495050181006003076000350540c0c5925070750340d90442d24001c4007c1008544a24141100030b603240003d503410902c440e0804e0201140b403005008030080030b1409030041c10f139400c1039410300191000b080c0c030f12611941c042c80050b0f08400d0707046010340608481c101b01a1520010306160203440b8040c2d01c000c0c103201b010381090584120728058200034540444075035845122902b8051b04151001241810740b5141104202030140c011090012400c0c0998007080125218440840d500b001959104085101030145902d032012020302c10341d0140e1246009420960794101103412402c0d0324010324 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 152596735 1250 152595485 152595491
    0x50708010c0e01141303140709020d0b0405060f10111603060b030f0723011205041b140d080a2006181506120c090112290c0a110d03 58
    0x60499030f403264400162a0400e90b44c80c1c94036401203410213a8441d14403005081984c0b400d1012031001d4180a01401495427000a56a40c10350700e1000313005208504c2521320640c0f500b4041441400c0c41b82606090381009880191917220044c4182e880c241800d198000600c00c032244450800282c079001e200551041c00c0c08038020030781038209030409080c507450313041a2b030250800300480d0030545039180e2140c42c020b1101c2454840c12004803515084010182030885c00c14040c0401c20017a1002600d40c0c2840601500409443e4918524400203180e201c0303900009030481100400e0f8840c1c01859842c080d4100841005411090455124000c4602c440290844420072051101d82081d2200382c0d0407076009005000702800001e010a000175050302e020361603072107008881207404c00c40c504550100600380e2a9560f5119039219250144400491b0100b9010070500d45503040c0d4000c003000e2800340342c80400240d136544c08001c0c1c550000f030004420024100c0d400c5842100500078901840b40942d808 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 152597985 1250 152596735 152596757
    0x31a092802040503070b0f0a030507110303090601090b010c02030303010506030a02160b0a050705041203080403021e0a020f031903030509120304080307031a180405121605010c17010e04050708010c 86
    0x1600700317409540110a55001085000c1450b0101011a820311030300303060010381034407150402c80d02c0c1d000e0104c500b02580f00000521120a00004031141262000b80090100100b1080115145101840020b40550082c001401113290001c09554800020070300141040450500c130b850054003804103032050a14502801150b0000b40030b4981d0120340c80c00d100c2d140c5850551114980d96103114043e04001d42d08012038101031081c091030394040104000014040c94000760103840d03818500f802c903c65401c4030b09140d058140810034001c07081c803c0702a010990040e4505031302600c80140300c1610390155030343e41058003010802450055006441c0e803505c034581290007600321800c02641c00d01d04400e2020007000d555078104141102565103a50308103c7c0c8451500c1403900313140c100d1030b14102e50003065000c2012143e000d121200c6015400078014400000d10a40700180035100d4030451980900050081c4800e080015030001e01c81c000721440a43d60f03821a90031651a900f0f2007001907184951 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 152599235 1250 152597985 152597989
    0x303050319061e0b16061e150617040b0f0a02070c031101030509010e0c060f0c0616180803030109180b19060503060105030d08071e030c0906031a0928020405 69
    0x651015140031403520340717049201070284c1200e50740c02000820060f22a15200310300481301035486240301d48842c00b44155005202100520000b07030148800040390118040746042c0d021003010b004941080d02c41c0307442e441e54285682c0c110002450400171980810000d00003c0e08251214003c5004020490303900c80003e0004042d030700064500400b40e0306140600c02d02e864007203511840c80c4000c4030865507a003101e40c3c0e80c036190b0007004060200b50050400300681e0020301c0702800d08240b01c03a61022640d15582e64070416884640c06620610b40c014401440b900002e58070407801c003000c481d04240d9508040d6241100030404441c0910650034000345900144a41e00900b00600740450281c00740d0f60401003c2030b510b90030010100d0801080001103002d070741c01001700000701240c10200f90758441d507601c00035000e0090107034401c0020701c0000e0005403161080c414154440c011030806a5281c82d0320040200b4010094580c19801201c25002100d403035484078002c010b8001c081000da26a80b400007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 152600485 1250 152599235 152599289
    0x1b0f05040b0d0b1609030b0903030f0603030304120e062b0c0f0e060306040e030301030302030705070608070804060f020c07031a010b090a091503121206060f09030305031906 76
    0x1c6240980c18404a000016822003803c2d43d005582400d8650038800c1140c0c02c6449540030f50002c0c1c9180c02e03c000344480c120300480154031075010403c251406032111400d01d9036920040340d0241080c12540b100c407078080d01c6540c000100040041055042c60b10030810405001081c1009202000d204c440030008001c15002d580d440050a00b0145003581d00280098059421103203c54852000000041c5a66641d540f084030710100c2da03000c40c1e48942c0c4920300a507a030345c04154160390703d01c05c01c1e0000480d980310700b241912034140740d964001b89484540d07a030030240802842216400ea000e01c40e038010070208000c2880158098119801c640c4c0098042c0601d558041e0050414038004020740f0b8550340310745e142c0d0380c00c84000b444000340c12485c0c0c881034000041c042d00005d08042c983e40782d2800c0164081c44c21064000484d00c01c2041c1581c4403030079942801c40c8d02c90400803411546080021a018002565100340b82c00c03440054201d01d000903104031a0140c101443c1c4140c42e101c01070b4804d01e048 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 152601735 1250 152600485 152600501
    0x140403080a0509121308010501030305040303081b07110a03021f030609050f040807140109031e0c050c060c070f080a0506010e040507090203060102010b040e0d110a021008041b0f0504 80
    0xc1c000c0246040444110380c8400aa961150310400d000840782c02d05c04201104000901e5214001c0009584034a4000c005038000e01c0b080c0c0000c1d04e40400300306100b075205d0240150f003259040d0303681b600391250340c0d241e007242c00c84a00541c08803c4c42e60000141c0c80e002091029030790141c5101402880c04035010b001c95005410204146142a00b000200140ca118207a0070a03009440740b6110720141c5014034016000d088014515420107001400301500074014140c804030700d0082c48401204608119201901020702400c03a9104056561150610b10002c0c40d003c3c0000054032403030b549400b105015041d441d4000c1840d81e10204009060090500c981c6014004c00d03015040107051545800366124407130f02401c3c2c8031a9000000c96401d0303000f584400c1940c100039200740800201120284e40751aa010f585d080468029140564002400304615003510360040c11500300c604283c000711490a4028070440f100c60b03201c0020040098000d4000d0b0060080070704040c08541003005200644080f0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 152602985 1250 152601735 152601751
    0x6040303020a0225120f0804090504120f0215130c08030304020f010908101a030d09060305090109150504030905060f03010510090b07140c19030b151e0d020414040308 73
    0xa261a04c0c045204074040858115202e82d45141c001030400140e2640705000c01071444000180001d0354801c560480c40c8624010300c0322568040e810641550300d80c0c0301c0703815200160044440c0141c10460508ce981c2c200130718000f4a6040b48941c0d0f2040703e0113545402c00391141d88040100401c6141407500101d07040300c00e10740414003078902040280d0b290001d140c80041c980c0c0303030780381c0d05203001c20001e9180804100404482040c040c1d0980a045604640134041c00a4281000200626014040c98000a90002c1c110140000f143c0100004200c00380044080026075940000c440d0f807060064002052050102071790795251804200c03488840104090912805000c200b11071480c440c00d9400c078541107406c90310318960480d55681488030382841c0035481000343c404141581010311404041d05e100f40d400f40c1064444100c0b00f4140780048160590000070000e20302440301109641680300040a044007441040640c001016212440b061016000c410401c00040c558480c405680100036 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 152604235 1250 152602985 152603023
    0x110d060308130b0f0301090c1e0c03090b0a09030305090f030d1e03050403050a050705010b0a08150604020c0705060d0618020c0d0c03120b0613080309090a020901090608040f020306040303020a02 85
    0x260413244200303400144074040c0041e90304c0c201006658095815072584244a84212480c01d10a14002d02007148611b0243c0002e164100080351010b00c080031509982590b03200d2500300b83c0703990341c1102e4960001d519582c1040343d040b07034081b05071001c000c0d0520144213031302c076049403490075003004a1000954640000301401e0070140000300b44c02200b2155880e030343e860710315641c103101c2c10030074058001500e034a50040c98440c3e0004080b0740200b5007052881cad02e8514480786c1d480b4030707040200344c2c000c40c284c1040c190800e100810203850030380c00030a14131a40010128a0035070304d800503140f041c0d00b6144620100d80001c0c400007a4401881408845c0400d820182c15090030760700c004201a031407000032100c1030340d205400b590342d42d1010300b80c031140e04840a11010550b101c400c200c1d140c0d0008010140240710740804170300e2201c01402511050541030b9610103210b40f52880445145001030700079071b2915056908007001d80c50600c401403041d8006d031405645c440031400d000380341400c07449544422500b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 152605485 1250 152604235 152604247
    0x30507141c0e010b03100e0c151603020f030f040501080717010308030603030c0a05070609120b040b06120a060b0316030f020d02010e030a03090501090b04031203110d060308130b 78
    0x800540e4088055038101800100034003124610b0303006101400182c3d0b41485103c5044920034843c0e0010041d80c1ca01000f0358600004060230300c0300344004045d40e040380038803d0103415540d003030000cac1c82c2040038000d03c101c9100807003c50281d03056620060640044a40000e001e01c445d58104880581050301e0b891711500d40045034040496040c818040140a0720000011807040e80c0d040003030707590f80544081941c00122a51515a07a1007c180c4262008540701c6100016148075034410a225140c220a03100f0186c0c0c0d0300d40c3c40e0000c902d8020304440d07211452000c4030207d0b036010040c1290b0030380328600c0012040a01020989402070b483c00c20f0340d80007080f0009000003001d0601e01c0792030340d80c19280042400218401a07070403c245040480d05071192000c54001d0562001349142199801e0b00d55005d10740d12401200e809100f903000c080d1156a44c0c50314445407034440c1e400b4003401e00411a409041140b9060103c01342c3e0000d0b032099401070b4010842084d40d16155030110000c1981c505000c2c5044c0c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 152606735 1250 152605485 152605507
    0x20702090c0415140304121404090b090108010912080402030115060302120603010501052404090509030307030e030f040e0415020408150c0a0f0f030207020406090f0b0d051c021c03050714 82
    0x5c0b100600003440c070180300d04029417450144030000e024034060390103603071250b450391a000c0091201d09800c1e4452004100006220308042c4554068650080b03d4140d03180a00041a521010080c2c02243c040d036944000500c20130b0f0680508010380741698004d0703501c1e0400c41c5488100b040141159200c2d0b40342500400031680c400700c55a108842030b042d4040c248405030400d00d0280100d901060540d401c2c2410040100c3e4044011403144080d03490400840301c0546141e9524080c011440d00324040404c0207004d42d802da4240d95500c24401c4c0d1b1402000762180503003c09a81042c0d1042c40d0950200016404059600b46055488422248003c1c145640c0140040000e200d0a096105101c496032244510900c02e4044644c101d402800510030180e0f01e00102c40209030707444c4d200c0e142c07d00d071544040c114508a080d010403180c000c40201402c004920100015506102c200c000b5881600f90844054150403d4004103140d2038600044a1804020140c106012400d0f5010032403400c2040207144 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 152607985 1250 152606735 152606737
    0x80f0708091f020c0a05030a02060a0504110603090a2307050d17090102070305070b07110103090209040303020306031e06010509010f23060403061523090a050703020702090c041514 79
    0x6158601c5860700c00d40b902611160082c800d16030b0042d55401111013940034031500000a0450780304583c200c1701250b66551881d41220800d880040900182044130201882c19001454028004006843c10514540da801e80f144030b08125881c0030001c5060713a0401788205000e403800802041c0c4002d101c3c007900380d4030b11115410f040c9090740c103850042200a804e03482000400c024642c40802c5918403501c0301d150329507a401c104011a500c03140c064821507103504c2070184087c3c2c15805023594180e6112139600780c0103900300416140c1c05210365069802030303540c81c0a21042240c62900602000c0d41080c1c140840e11005800188809032408c9080003c0d080d40401d08041084a4840c4141a1382c0407001400d28482d5500c0070342500c0c10055840350b204501c17180303003044a000d050025000d000a0907000d000c00500c0d402c3c80c0c3e101c86110001070002c0c4180e040b5907072000705407400624101d06503000407200081580c0080010f200440c00b40000f5071145181120043c1c181000e1110100400054041d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 152609235 1250 152607985 152608003
    0x50102030901120914030a050705010c0509011b05120f04090f091a07090b0705011406010f09030807330b0303071e020109030602031306060e060303070828080f070809 73
    0x1500d99882566040c01860080e02c1c603495510802d0365507c5004110081c25500100c10076219940b0700144c0301c1c0d01d1070240007151554035068403001c6600c003c21001400701b60b42e032070050300c95002e460001e840c2610498010644401d040303c060342c84034200303c848000c0b074151904c05000180350210314000300309400a06154440d150203854800c0c0d40c0c1541c1102e0b0031035554418818107a01040e454204072040d0400071618008142030400b0b0754508004454034881714000c80c0105002c03600a00104a00ba001000c5d40d900407185107403842c28041e004103580c1980f2100c0003907010724080389045543d540c003480c040321104034020340c103140c1c05854100001000d2000c1a00450f641c0440c0801c690103174980000850700420215180e113046100444420000c04c41210650714003033b8003290a00c20a0840c07402664094015400d04025a461446683c09506490700342d00342845a000007803129810150719035000d40d9800310310f06001d00782101600380580321000307100422040102e140e0002a00c045 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 152610485 1250 152609235 152609267
    0x41d0603070b041203030608010c171b0a03020d020403141f1a091807170f0604170901090e0115030f0b090c0a0e040e151803030402040f02090d0f0606050102030901 72
    0x4d2464083c5010343c018003040e8010561035013418426140990444854105094081c0000e03c5c540e940c1e440302e0902c4c2c4da409081c040741000920031000c0d0a80b0031b5018080004602c9030061406840b81c845185101c00742400501d142d100360b081d1041129600c8480308a445152001e005540984e13040c41b04a00c2d4a01070075000d06000c800040500d26036900c03001c0d07143d900380181e440c45030f1030b0000070301810114542e00310740c1d2241c0c0001490000c40054118030541c2c0082d005182c0c01180c40c5400041c4c1c1c80388010380c2c10880701c0700020601d030b4104192140204100c0010141c1d1032001440a000d0311800f6108824683c0b500e050000584c940c2c0302d43e5a4884154000c003603480c48055429181207002030f00c0160000c0c030b01041c121781400c002503044240e170402180301d0b280d070356054103400c40e02c108801190b055810030b2002c42c0040c1800c1e00305070134802d180c42c405800c004200c00400c04601e41ca803801c1c0e0707021f580900044140040b42c411440985800c1c4061072070080800000b80040208200c3c0c00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 152611735 1250 152610485 152610509
    0x5160503040c05060a170a050106080105030c01170403021e01050f01050607030806130f020a020109110316060507050a150c031109030304050904020315010b030f130f0204150803041d0603070b04 85
    0x550305e20311a03420415540032448400055082c012500e500406017401a2000724429400104281c5000101c22400410507512109502d0f00f601c1c80303649100001c0c000f1010340c030440c4070803003400711080000c400511508000117071601c3d04205c4500c0e4500181c1c4868010362042140e403000c00c0e0701000341c0d0f80c09041030b40c488003182e054030500d50007841501c0c2007180741480070440c0400d9030b80c1034002c0c0c01c41034024004450030b1004a4101511041c901100c0a252100b0341d50811045c0c1c083c00c06024810f004400380d800791021030303c61002c0300b000c16460140c0182c0e00c5000101302c2d60140310386c01c04d01540b0003580c0e00704400302d804641e5910039802440d104000d401c000508640d8104082900d8844807508030b0240c1d6540d0882c501c85030026188c8a24001d1094005260b1460314038400504d143c00c081c0e8001141d800303400348002848080c0c018280d0706154400490000020001440140205482c00351100c901c2c0082594a0b0300280072148290010b00d070411640100c24251415200c42d51428 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 152612985 1250 152611735 152611747
    0x609040818120106140a0b04080a1203020903011d1e0601090b0a031203020a0908120706050c09030f0c040f060b030106050c190b04060b01020105040f0312060807030605160503040c0506 81
    0x502c00e03641c9841d4030403071507013040c00108031000101d41040e403001094824800c000e8481e002030007a40201c2c003c81b106c0342e002801e01008145400b0040c2080c83c01800c0c01881c0031408004682529607007111031012201100c00391020903410004a07204011103070180c2c0e44d02d01070341c8000d911408107100710320401c0c4d250900481c9a0b0340386407010300111380c08040c201c03060082c031a0181c041c0d000214240c001c1907203200005280440880e81c0e5040c007440185062508596a40d950b005100c05841003c4030401445903000a84003003160301800b031f00b044000e01407441c500080006440f002c02001ca086800c00c40c003000101009016a070658006007081a15803510002c0985000c20740c0a9400040140580000034002c02c941e000c4e0049009400510210164600590a94106860082420180b0840e102c0407a11402042c260f02c5d0360114041112a40e5001c02032601c0c5040d002034030303030a0b070b144140078481621743c0041c2d490140d41d0812504500d090307100d81c45108480d1003143e01402000600c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 152614235 1250 152612985 152612989
    0x105040b1f05041205070f0f03030503070503190203040f02040b0103090c1403030c0313210503090d0606080a0b1005010804030207030b0c040b030106020c03010c030605220923060609040818 83
    0x50f10041e00c68660f00c801c0400c42424402da43c0c417214400d03910590030701c10000c02d000c07a000c21038030252601030310784030f255440300c1400b283d035540001c008042e015800c10800b000f0180306c1c0019030041c0e0180c4405004020140104401c89000c101c105040c14980b80c00c3d000002c07d000c1070078003240c0206500c041c2c030101e010702007030940c030801c0b655907103d0100003001c1030100541e812000c03c0d02d107050b8140002100b80ba051184196100742c0192a80d0300c14000d4810901c0d00c1707007070100850322490700854141e981d100c22510741311501000720b420610510400c413401c118820000002d01092a204a0901302500d005e52120030902002d0045031005c4001010b030713004081140c0c0100218204541d4a40e034402c4000d4503141c80301c4100344a5401d007241882c070130344640030782d8099440050050005a18114442c5240ca40c0d0181c042d054685801c9580007044001001050400c4c64000700086502099100b40c24031000600e0240f042c0585800d01020602170016a810201481607a00c2e4514040d40 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 152615485 1250 152614235 152614237
    0xc0603040602070c0e090c030102070c09022d0406270608150d0c05030f070b09040b0102010e1b091e040605070e090a1a060c0c040b06070b0a0c080105040b1f05 70
    0x1c3c040e06140d00b908001540c006544c84003441494a00c05403551800030070201030a030710030301d5030181034149008810700c010030560740109240c0c0380ea18008641414092050703140b24a449010200f800c8010804015154010403090100ca034008566560300da240da50542d02014140030f00380c1001108000203000c042c4401103101c0d041c500501d04110f0200d01e18111218040600449009019041c0d0000c40103000007110b0040d5000c00100508140740c0c4004c2c007004210410200e4119901c5000d015540c3c4018804600d047ca5807000080a216070042408054600940819000301e00c800265000701500204c1580040d4461004a0780c2d4032031030012180342c4105524180e0140420042c441002d502e0360122102d401040c9000c60180303481c4080100f140903004040740c0c160800003c16080d8900b551100308040c3d0700600060505c086520782c60143d600403503250100c15a540c058448583d0000c260b00e00600c012103040c41074403061070108a140320781c006c0003c05170b03001d40c3c0d03486441d60281d4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 152616735 1250 152615485 152615497
    0xb010e040f080f09040e0c031f2d0c021606051602030d0804062003061504150909050105040902221b0c1703131e0206070b04050601090e0c0603040602 66
    0x200b020350700c40092640040c036503403080114030f02c910300c0c000380c1240340c00340070401c2e120301c401c010040c1c50452228500c58500d611001e510a400540c3c3d05030310310001c9401d60583c0806082c0b555005010740301e400d0754004644142203410195072107018036005500e081401c4600b07803002c5190660300e50442d8058a001c0f0b484800c0029454068103103c4501d4580c001c00c03041c445c9010302001e00001d81c01040004180c00b000850807021041000082c0311740c1084407103081512000c0e21203500c2c0c96aa50740c1c1326643c100d078181c45000241100d604001c450b2260103020301504003118208900d26465000800c0580303100c010199105998551441c00c001546c0580071140351100407080c9400440030041c214030b480402114070021014100442c0c1e403003041640d119064000c0c00e00b0030040d80e0749800510541c0b0102c0e039020700400e0311103240180c9404028042c1c00e44035816070211800c203032a00508000d4140c0140e03518500d0450100381303038480001c5c10100346400b680d0541e44e0340c80d54100b8901130301c500 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 152617985 1250 152616735 152616743
    0x183c061107030218060a05040204060c02010e030f010c02060103140d050403020f01020a020a0f0906120506060111010603120f120506030304050105090f06070f020306071403160c06050702060105010e0d0b010e040f 93
    0x4ca0a900c05200300c9809080c42003a04076650400c484e114403c11040f4000c5005802c0000c14003d41003005501034103525002200003022507400000d1100200c0c04c1d120820040801a0404401001082500c622a600840d012405080e604080d6440100140268400680314882d020a100c0c100d90003032050241487e00500040955525203401041d0180d0318450110042d01d03016002800000b00040900d056511070050714040d11042d004441c40400300d510030901d5562140b0000c000b42c6036aa00c0e41068159449004000c408510701500c084409803c043c00b040c1000e04000103540c01004440544100342011521500c081e0041100c0707901c2500c8554000c28005011018054014980800c183c4200c0482d000740e03403a848206c078000341e0500740e242c07407070402e00220707010300074000441004000034a460310380e404040c1c0b80c41c0141c50303003560b0010142c2c0084005009559022242c9162010162140003440030300359210001300b40305109880e01c0103481400300d410031421604107a252900 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 152619235 1250 152617985 152617999
    0xf070f0806041506080118090206040e0c040b0301030f031d0d0b150d11120a031205131b030b090a08040b0f0702060d140a140a0c183c0611070302 64
    0x130307000007070181c2d1028001d03610003000155055407444643d00400b1580782d80900448e050500e46042c2105804001e0314080a4050034000882c0c3c0c502c0d00000b40d802140680d4100820342d40d90b05000c1e1985040d5a01e000d100300c12006801e40d9034440568000700700d68003c03404281aa00c03c15441034000c070390924180c0c42026410a4070a105130a41500460a4111aa10350045413590800e546c0e0040e42001004104c002c414002c15104950145a101c00b040700c04030340a03940d59880c0814a00d030040103503c1d006d548441031051001c1d000100d1b6011054000a180407100c6480b00300c401e00807440fa01281100020700500700d0300c0c9490a40d0040c0c0d40c0a4901030702c41b4809152003025003210300d501c4255141e95000620880174a00800c0031898244041818a4039007442d9203000d0541c00da003020621044441030100201c0c000da2000050150030801c100c8941d001003000040c6021100c0800c144428203c06102003900c40e80141c100d81c11400c10b501310000e03030440740c0d0030851654006940500 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 152620485 1250 152619235 152619239
    0x2090c040503010c09080f0607090603180c0b030a06050301022505011805030d0b010206070e060706240303030f0903082409150405070c051f0f0903020c0102060f070f08060415 77
    0x17410040d02c1082c2d0310040140c51203e5a02601155660030413030b43c0380c1c00614524010000ba9000781e002c0a184d40e21102401496812071300d620400c10081e50041e02c0c000d1001041044000c4544100d0015010880c0250300d420100c0c407003c2d152162a038034281c5601000c040400c01c00800350702c01426100508610740800707103a82041501c0e5000450a106100c1c00c1040d0207a4542c8003103005803050030641c40b04140450b200041c05860303081803030100c6102d5503924201d00240c00c80404060810b070f40142d550307030341070441c580182070b0f035490301240180c42d051001590001c0e8010f42c0b03d03035201d6908140c1400300251030500b000000c07911010603401c40c1c1c0e142c045c0100c0003c02d04501d444880e013540c1c1071005171252107080351040034407600541160400d241c0308940e54180f00c5101d16201001d00c011901246a040c030104803403044004078056444104030f8144da58051003110f6009c43c4880c0e02003110300d403414002c1c0c0b03031300ca905031103208009092000070060343d9140e00c00c101c042c0201e24603086003a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 152621735 1250 152620485 152620487
    0x54c09030e01020d0905061605010b090901020a03180b01140a030602070302030a1707080c1305060d05060907141e0f07050c150c0c0603060307080d0206070e0a030f02090c040503010c 80
    0x50000419030044c01080d2041c6440740c01a100724007102d002802041c5030100340c3c0c40800c5420a8242c2c01c5466540721400d16030ba03641c60070915402081001e0005030b54410005020703081b502480074622202200e00d5807030000c1a4060082411a05042540c0500d100d803d000600d40c2010354000429191010138100c09146e03001018001107015500c5501c040030001800041100e012503840340082d2030172b03001454048020003e070454002c407882c142d000a03203480016405820a00d14220915603500c20041c203450310244032500983d8a007070800c2d00060150b43c440c15031040c9503040c2450403141d03418443e0031401d10101d41c0f03190101010740391107941515003191528401140c00c0d1007110300b01c0c4140508800310003201c88000340e840040203000c201c1018081d161300b00920260745401400000645d4010501c4002c0b0f104c2260307409000945460680074082d200c069075054016a40e0500c2400010b61340d002401002d901182e1070f044076564651050050b101c0c0d500400e0301542442c1c0518801c07 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 152622985 1250 152621735 152621747
    0x80f19090509070306120f020f1c150902060f070314030a0506040605090603071217120907080c090415240602060a051b0a0309120804054c0903 63
    0x65407040301d000c8034a0b1658042207054030317000c0c06007440201240118200207035441e012481880d03c050100c560040c500400211017401c0581d0038421241c24030552402c0240c0c03001c00200d0210415070030440ca0400b600403e4250082d0000082c11940c002050414507004c1c0c880e20b00c2000390801f91985c0c91810484140c06800181c908078080d42c10700b04003152034500351840900c6400054000c00341203143c010306042c0000ba510054408040d0708444009900307a50005020f817420a02c8017084504196404600d00440b5030b0118000d6000507001d62450b603142844150403503000b20381d45240005604240e03000307140c00d0841e0283c030f1906403c10b04180c24082564401c84071180c09444496840000384429288116005e21845480e120718191601e0902c01030b003100d00c0315203030005551050f5545c80b602d02400200443c007085080b020002004020400380d401c0c8081000d680410b860080c2110031001c00c40c180d0300c1800601032040e00700c803009401f02043c2c201e0707130301005008011250601a00c2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 152624235 1250 152622985 152622989
    0x90f0106090c110106050105030a020901110102070f030f0807050406031a030f060a0c0e03030706021b010218090105030a0302120901030902090a020d0506090c030103020103090335071b080f1909 85
    0x215100300740d411050f0780103120703000c02c031101030711490724594603c07c081d0020b40c8086801410b0000001c0081d4200b8001d201a081e501d106181102c0c0d1b441003400c010f020024018000e40421850001b082113040d4080b0588080314074500b808140e0460300103003000c2c21405072524507010f108490481c0b14900c0001880c500030740c00d100f01000401001c1d10107c84070041602c003503806500070000040040e0543d401000400c942d404c0e80314150f120740d234100e804d80e4070400c0c903841307003110030b6413603d500b0300e0030700b07025401840120f004002d890096980031351100c010f45901d05180c03801003018603881e4001d0f0000101154000c00c034600500d8202440c0f4025048508900c0710306160000003951824004002c60160310140003036401c603803035030f401100940f10540c4200d040241411140e24102c0c10800c16000000359030741010b02c90102c1d180c2510f442c240081c952030400c2500340b010078020b07619610390b81d0740030b8000ba105a0744903000b20ba8640a4821002c40c09040c0004004400c0c2ea07590010f120740c1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 152625485 1250 152624235 152624237
    0x60a0810050604080a020f011b060c030c030c02060a05091914010b0103090f0602130906030302150906010524040f0f1404050708180f030301180f0e1203090f0106090c 73
    0x1192a48a03000c2c007900740218007402c18103a0006038008050700c0d044e5840c5c3c08214051510400c0303501080090700701c1c002d8219081341c0c01030300c842140c420b0b903804d0700400050751500d03d0304000d0340c0c1055100075079070714019004034a52a61400881c0800318203000c400941d84052407000003040c0740d0704d01401c1c4d003104402c1400c4554031b041d58000c400d51c428041d5040315134000404080c0c86482da1554802544090708902c502030804000080125040c0a0711006500a80252041e041301c03142d12040740c0f1001b4081c0c0c6554004074014403055070354000c001520b640502041000f52200da1800c0c0c030500c11a000090036003103a190004100015544900030b603800710183d151203103c2081408140c0d0003d0f1035807030204103c040051000000d2081c54260101003804a805041c1200d01075030a41d402a00109000d19400c030611141c0c12a07402003210300c4404020400010400e800510b480e009015070301c5111a5001000c500d011000f0440c050751998030700c0080181681e40c1070410700030001026000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 152626735 1250 152625485 152625511
    0x7050909060604050307171f09110f090c0a0e180117061603090218040309050f030601080c010c0203030c0f0304050a0e07020705010f0c06020409090b101208090a0302060a08 76
    0x1072140c10054240c50880f403001e802004c02c01c0c18400545207155440012103001c3c41821504c03402c2c074400e00c20000c200c05d82e214002a0f00055814954a044001014207000340c4038001075802c0340d19048403199000012090303898540784002400c50b074003c0701a10a5034841d5259092618038110880100c1c12500700444407100000240e20385038a6940c11120200c1d1058481040b0f201035010740c0080364500d200501c0502c1010401c0c10f0400306800550b403c1c1c00003503100d00148060708094a060112410440081c241e9614140300c0d2540d8405074207503039040081800710042151000c0042d2b4405515440c261171811414010300303a45c0360801c0c0b0030903100d08421500010456031000400780965019405051100c3c180310064564144108580c4200110501c0308404168184040c10290514081c081080302285c2401c503904c0c03001406c2c603401f42142490400040341221034428540380d1141019440b10030b04030020704600f000741c0c0065045a400940014603541c40341e440c82c17107551070003022 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 152627985 1250 152626735 152626741
    0x60f080105070306120c0519090c020d030f060e16050c030c0c1009060215090f010e060a061406070b091609020307081503070506130803130e07030212010509060103110307050909 78
    0x3505d92601c040902500f11040c04105104038200b81e403860200781243e91445a02565844204080b00c0e4560400001078110440300c2c80981e90500884a166411038402d1280714104000300d07150390005030000900151a5210300013140c010401c2c0c422000e000b00503241c40d1940d0a0762207444122014105200c0c004000203482e0b007500505000c016202c00358002c11001819840420050b907026000760110f200311440840c040009000300510382c0010400340600c0d04008001209441c119003004114a40c10110401151510403d5842c0c207070308207582104580740c90302d5240c10300340c121002c420300400300304000c104a0703681c1e00198025842035866130590360b24400b01c94000124004007075416003080004200d280b401c080504052502d1081b6004202d0f581c401e680c2c81c55000407003581c00101c0d0140304000030240e60510580c0028941401d40c030f029281e2041c02d0b02020705009651081ca550307804121580d220398400329100c3c058090103039136402c104c00007500c02d400903072106104800000c00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 152629235 1250 152627985 152627999
    0xf12041412100e010e06180c0127150e0a06140903070906030b07022503060e01021c240806040311120703031e0b01090b0d060f080105070306 62
    0x226400c440380040c551441514140421094080c90501465148901880e01c10081d14502c90942411440000002e201c03042808182c2002ca0003018548192100080403460382c401041c15658902e09180c01400c0c0600244806903240c4181c403200198075002c0b00c04121000707484030082800300315848a9030403211390310030000011024056100004e40e81804482d03051900c60240044840090642d6549030311421140119101640207442c10130100c82072000c0d2a130103200d00524400c00702242800c22a41c20b15891a030201e03440001d090300d81e6442030703c1d00c8180a5061360740c2c028103c0592075516a500c1080401340842e00758004180c0c80c030011707601d07951400036000c4040b034642002425083ea03c68130705544030703e582c01820410740540031290f00030410040051102910030b8400103180b003121006074101c132400c080c0011080740740031031046190781c010f00c20004403104000056070b034050041c40749002d0001c682c00030415284200000c2030408064020901c10940c6507003c10803175a488103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 152630485 1250 152629235 152629237
    0x30e0a0515070917060a0c09030f02010f120c0903020a080d0212090d02090103060e01060e09100515030709090506060607080417030f0309030a08061909020903010e010603050f12 78
    0x8005080780c0c007180038584024806403a142c2c0c000701c1ca080210046135140e070f08484840341c8101d44541600b01d0000c101c1680858818000311400300d1900038403040c2103a81789440b981c141000a41440f0300e000c3d030101c10a210307406038a00c21426170014400c0b600c862001a08600050204030310680c5200408180c0350400152001c0360344959000b0044090344002400b1182d000000300d60708401c01803942d001507214641d13054000c61050b01c0024002c0d00e42c1201078216542600140c00d0200040709210800b0400159034460402e0b00c0c40005a80d243c039651030030b5089108950703903094022410000386110381548549051070080c0309881455940f0410010360b403107040c200610052081c0420701c1007400403c1d803214000c0031201201d1809190134800007443d001100c03941d0081d840050390105480c0d200441c9071300540155a041c004041c2160400c5a103040e9004600021f030307010508050a0b0381c03d40210401002c140020804141c0f03905007243c990340c000640054503c103401031000390501d0f0300 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 152631735 1250 152630485 152630503
    0x20d0603050c03060f07170a020409060f090f090b010e0a0603050f0d0201060b040b0415030b03010207080315040509060a0f090b010803040305120403050a060c050d0509030901090602010b0603010909140f030307030e 94
    0xb680307104c05e0041d001c07d0790b01d007800c2c060001d0403080d03400d000109551809205220181201c80d01c0c96604524000180066072100040c2002d464200000503000030300d0a140d0760f066030b070300c6003100c031007940e40048100041a5550000e07083e0702c11486c1c10a503c14010854440e904010340c000e012030342e1078a034641c506220340e2082d0400383d0800c12040015000e600d0907242d1918051401189104010340002d080e45c03c54901520008000014044460311100083d810404199418006460b0060302541c0301c440c0200340fa040d00b91904110041701c100b03540300011480d8005000c1c022541c4a009480e9039410a01044030306c0d10400320f01091000f80e510555045035445001000f444183e90707130303a2000e40b400070271940138840140440d4010740d505000755440b41803440700854688c46074100050034211164000030a59240011094068640804983c19a2404400480c0c071002501d4103031510307502480c9410043c01400c07000b0040c25800f000850048001d40d03010700c180705d00085841d0701c1d400320b0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 152632985 1250 152631735 152631737
    0x801141012020607050d0807030e0a02010e0909010e0102040b03060103050105012109031e0c0201080604020a05072006070f020301050c0a02100b04020d02040b130e060901090906020d0603050c03060f07 88
    0x900c5040080c8005051520711181c40034100e9810300030725581e042d14000000001d08007048020f03080001c820344c544190300c0c00c00f54290003040c8440d01a00060402c40004030a2400f9540110008050603025080000c030300402100845d540e560f551034104050b0020745505000904080c0000751540c89282c0c00c0301040c0c22103107440d007102e401000000c003c0800000031014044d014805150200301001ca90001c070090340c84401d00c01c5164800102000d400a00e003d1060303105201d6811916408001d41c0d502c0d65102400500311a1030380003821801e115154080d50100700010f0f100104880c0448001d507081c401d42c002e0200340c03610101e810041c001d003100000103a0000d0244400070300c0c80e800025002c0c502400c018036184030b1413102d80c2070340e00540125150400005002902c1d042002113280180655003901005081c0300300041c0a101044c4550400182c413030300d80e001806110303811190f02400c080c5040124036501d00e4110340302c40c401501c6c9881fa024440004001103201c0311100e1086000b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 152634235 1250 152632985 152633011
    0xc040b0409080a0f0e04050c120109020c03091302070605041a0123060307090302090702010c020f0c031905070e010f0e06030c010806040c0c0210110706050c070504020306011e030204080114 83
    0x31420f04488200300586000c0800c02600701c00c00040d26103208080c01440c45d800c1456450745040040c000c3d844040e440141e5141c4108900c0810315808005d8903040d00c003c40c2c2c8000c00c0040e482060000c0d00a00501421080c60801400b0400c5006071500e24220240d41d04190160b0b6203000911000405081250400c070560020b0070251900070300443d803161450500d0214191242c010030401042103403a070015030765601251407070301c1d0108008400c607180900246103046402c0c0200b03440e6240480c00005015a0100d220700308001889400040c0c450300e1603d001640e51450265080002442445120801000403070740714100418140c040c5541a1601c1c0450b80740c00003400010902900c00f50204070003600107600594810301291200c81941d92080000540b00140307505004103940f01c4030038400e0800c110038003000c01140031070854000b10340058590b5203880040c1c0c2d6505d0482d0480300d40c4802e0b45070030700e01c954041c1d010b00180c5100302d00030400d810005140454903c820f450150700c01034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 152635485 1250 152634235 152634247
    0x140303090105090d0605010b0c01200910091211011103030609062b05010b0405060306010602210910030c09060306050a0e04060b09100501020c040207110d02041d0c040b040908 77
    0x40502c00404884a002c0e1558095000744d0b210002200c4013038000800c01400042e0035440b4000034056248156076000c42040d0194280c250003103e441400c00480c043c04100040c00c0d00b4501410846c1e0041495240c407040c00f80880c0b40044a8040145942d40440c4484550183c0540000262031003000c014101c9541502c4c2c0001b0000c0a0410301d21a0500c0e503014052054907692819280368410712031000400c0c42581001044140e48008140c0c1d402980060010080c03641d0004200302103170907003000100343c1e07002400c01546e240305400c00c4a03080151841e42c000010780c15402003540840d55605c082c20144c0b10712049040e64101d119055015156840511800480c01007098120303100d0b01d0000780100c00c547c0852224541140c007040c281e0490309080080f540c05000700344040b68119001c600e040856a1516014001d00c00004d0194400e11004411525554401c184c5c4040d64600c02c40406003074040e981c1c0d10451126214003c83c149020303a06541064020005400e500084d034600b810 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 152636735 1250 152635485 152635487
    0xf01090b0f0411040909060213060c030f030f0b18040314031006030509030702040905030a090504020307200705040509031b0f030f0708041806050909070f0b09062107091403030901 79
    0x5100d04104850390020080000c01d2200c43c8242d41034641f0030340b009078680049140c09039414001364090740900146140010000781d02a005018055041c200001e000e458103001c00000c048800010382c11880700c1c160858480d0910341c0143c821842507070740310103880100719203c5d2217000030386952400701ca020105000450098000d694003440413000c03a8140402600000c013074a5045009a60395007000070700c0d100c1564884400030242000b83d030151b24600740110004c1280041e058880c0141008040d05410304005002c24001004020700038000380c03d24048594030b82e80080b40030030314800410000e0079a2140402e5100c1c2c1803c1d071030095030030154500c0207200c0f26032000c9021110032200b0000071075966005960755625444a650000302641000e00380a09910082e0100d8615030110f18104294040d06850000b81e424041805848071242c5010034010f000b5100c401c20081c0c0c2100d4140c1d66241c00d41c10b01d03849024103039904008169a81d03140003400b041c0c002e9141d01a0010411070311a5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 152637985 1250 152636735 152636741
    0xe1506060705010b03060406021c0209130e010207060e071401080618101203020d030606050306090106030c02030c0f0c010212040b0a03021b15060906040b030c0f030a0506010b030f01090b0f04 84
    0x1840c00b8000100d80c0001850001c1c2c2009403c441c200c41d8107902150440d903e90040c0c01da50850304240c07204500d4070309110006412244044594070942d500c542102c901c9481c01e4041d03070b1041c1d034840018407269034110380c05511400c581c02040020200404030440135880341e00c81030f000d108003410841460b01000d511001e02c0600074801c0c1c3d4a44884580020070400c030b00301c405a4180a94080d0107980420a00101607955a500181c1004014018442103544c2e00040e541103540600300080c0300c001e07d0106a0460088440142d45402811050640340001250001109000b64251104814a4960001c0b03034040c50081024048081c04145941c5000740e00900036641e5508407040e071408031075049442c0440c140c01c200101482142800070604000c04a2500148100d4060282c0c0c2c41050209540c0ccd54480342c424840c0300d640440c401203840034401e01c42d4054000301666055030716038074000080e51041d540014104000000010f02800034403d00f241c03850024442200603402c04100406 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 152639235 1250 152637985 152637997
    0x40b07020a080301080a03020706080610031e06080a0b0703050408120903090d0302102906030a06030b0112200901050607021201050703060503070503010b0907081504020f030a0e150606 81
    0x80d8400d448103000070482081c05075001384842d0b002060f002e007061400a007021500c0c0d00070402d0000c01030034030a1aa5411030b4072403409040740f400003044107652803519546200c5681201c0c845140180c0400c0021011401c1c1c0905d40c0190462111501c400f103040b411944102c0300940704440500c40c151464490340103054210194400300d03800c0c002030100141d5106a0780c0c03000c0380945d00c080010b0010541501451200c0c04c442906e1a9030700c11120038401040b41181320070362250743c00000141001c83c10354800c101454010481d06800c0d0785640e60748882c0040c0e03501c1034880029a2001d0883c107036100d66400c4232920b000d400f41e451b42e444c200034840c0356042400c0480c0c1c00078080d100c41c2c40e101003d214451081225540101e030b805d00d4a01803600b0582c95401150080e41000d416044e2a11030216460f0000158039142c0120b40d50380700000986000b242c0520750007800010301800503200703100078500803000c11b1030401c4031201c2e000b11070355180d1b0410384850350811070394002a11840e1040103000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 152640485 1250 152639235 152639237
    0xb13060f050d0f150e1005040318030309060e06042301080f100303051804050403021b0409080a080c190f11010e0601090b0d0b0408030a0c02031c0902130c1d0303040b03040b07 77
    0x1402041405c1d402d030404640034103580001d542c1300200030603d90310078005c107492aa40c40380244810f0940d01c009010305000d014600a1041010303556803e511840d013141c0041520980284405801c82c0400c6280c098030b0002c94009144c0c20003094648020507180c0740900b000030084c3e18000e10319901607445402c035441155120214020081140c0c031503004440c4658480d502401402c210000f030043d074003140c900c2403801140b0700100000010484011140318018600b401c001d2503131030a8101805100e00d0800c01c03210600f44818000c000c0d00141c2c506110342c0180c481c4401c2c04202c4255600b2249105004201c03503110000420140d40380d6480070440c040060a40865909580c964191f402c43c01d0710200c1d00301500000b00314140d001c40c4664aa0103c152020714600807500800e1001c0851864031208003640d03407501201103542e04c00b10130103054040501030114076840000581540c00760b01c0c400d900d0400500d0601c280b45408002c0710280d5070040c00c81801c0d40c4503904d642004100c0180903034 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 152641735 1250 152640485 152640491
    0x706051207120203101503020a05072a15030605120309041109040c080115020316150603150f0609061a070606030b18010c0306050108011205010b13060f050d0f15 71
    0x7040701420340002c510401d005d01d0014800391508a400d0984601c5e4082c1404240c0b05221442d1081d03841422101040d402c00640403210040788980c4070301440800140e00d0984500800080a420f4100b0411111009071002c02403145e40d4000c0c49084c6480707492800302c0c1c1d08200000480c40c502513000c0c8404256880200e820a44050701040c1215202c000075004101900010051075080640c90001e403409803010b14101400c405840c580d0110211005251110441601120558070f900400046820610000c00e01c1c1d0315021b100000c2050329544080c80e42031500101740c41030180600011202c50843c03102112039202c040c0500c9030003481c412283d4a449030400000310b000718000901648800f480380282480d84842c0c14211880005200240f43c00c0110804c41c60307820405242c1101e414070740a0b001010a8a46140140702d1202e8882d44015400350980321441140e01605c03e0320340e0902d510b680d1039281c00401c201100c8004c0b0013041021181d5003100011903400c3c030075644103150741001c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 152642985 1250 152641735 152641757
    0xa0222090c0803180409020a2702030114090a1b11070e07020105011809020904080c03070c060801060f1b111504030602070618050a020603100308030103050a0c0501020706051207 78
    0x940d0241240d00503101a4400725010600f03440f08086607403540004c80b03082059030031b140e01003000005070f072103096a0a5580401d80d000180601da0807205603114207000c40d500d6031a0049101c292036a01655030082e00b10b5000151a0691403040024031303040208000400c241750342c1c0031102c24520001c445441d0040e1000002e01c3d81c3c03940300d0a4016059500003181640c1003100940114011403118050b160420034034002580355800020f40054008060559821503114468607500c5489002000210101c000180341d9078492582816224a42d40340c0034150100ea404070b0341c40c00c0341d5811080c8003072280002c00010b02c510b000c4050300e6402a0114040c1c2c1c4545840c410550071079031041d582c0e03075000201c81c42040a240300340352116404004420a02240e51120341d82da9011a500034090100080411030015041c90b1034802998448800c1d0350b0b0b50307160320700948c036000c000303108443e4910f01e020040348a600215048054411030740e2400e00300350001000010015001d40340c00240a0314a0b10 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 152644235 1250 152642985 152642993
    0xa082706040605090105130f02010315050d030305060432040c0b0c0d030c0504080a060e030c03040b120a0b09070f0912080a09050303181909090b180a022209 69
    0x1640708900075080080c0916082c2541425908018021262000c82a040200044240c2928030b0325036028a000100000341d0100b4443c1007100d6002164026140c1d0441f00c209503040d00030b1071283d24280c400b0300c1000032102a00d000030381d240a40b4554440b0000fa09403480c42c0c07005c6030991050140e0b4414069a55452100c0200d500200c1540001d400001103004480e80601500c4001e41003460510b00d82403501c0c01c507640352541c50328010300154503000c464424001c20400c0c2c3d11047d45d4003041d649d480e51b442100001a500042c901c05050b00d05500294032010703244955910b00c81c018101d050a559803020883d030082c0c002d1421002d1250126000c81c00c0301d10910400d401c0c070b100b040340503510309008402500303511080d84014402d5004200c80e1003018800006140051404d6031000d949140d060000000340c0e480d900a00070003440c00441e10f040c000c0c0d01d00600d000e0b81961084071030f114510807000303454103105c140294011509800f90300d50b412000c8005809650300e003500042c2c40c500c1e503031 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 152645485 1250 152644235 152644243
    0x90402091903140706180902030901110f040f090507050708030a18080301062705040b270f0708070507110103180b0a0f02130b0702030a0c03080414060a0827 69
    0x1080d1440b00c2c0c120b08040001a013040740c0300240409040030700710240c1106c2000d80d910160300611003000d40110214059a00135084550100c56481d2100e840d20031803070400155410070712420075143c500c81c500040d840c41e00d218440c080c0c0060f0383c511f4075000c01c58441210346d510151807640c11640e90414000c104201410f00303c1205d02c1801d54507925403426500418140302020340c203d442e45524100013161000703c4081007100c00503180400c00d0740c41ca40001d541a41c46034041c80303480c40c0f4880c0910310046500031552055011440d01c851b40e0f00c2c3c04d04102c0301008110f88842c0402c50400080e404980e40418154000105160200d50f80d0314400550b0400c082c905400c42d84c1d40c91040a01102d041d030760241c034016030760f2420218240f5001c104607803100100c3d44112007103c000000c9030000d5441c2841040c20264000b0020b192a541d2803800b003801c0e500c40e10916000440300003510b011480c000046a861100036a2166441d44a814101d01500210140c952800e81d031400c403a041140144 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 152646735 1250 152645485 152645489
    0x2010c0b0405100b09090604020112090b090a050d05070b0c1e0a030903120b030a06050a060e010f09050105060403032106050d080d0e0c060418181103100506060904020919 75
    0x14064114180034503082002d40c0d8881404034401d2040008001b00c0507000110715510680920b850060140c960101000034043c248024140400000402450000000d100d5510300d11036003c030342103440c6481c0d0864450040c107030004e001c540f403c03020031800c0008201810428080b87c50481d500e0810444030300940d030210b614240031030707228500f0105154000c003543d102001036650511100d802c0c5070020b074030f6048000000b0041aa25130120740e51500560041014040c0400440785c00d5841e0718228040c11405d00c9082503a6040000102e02414070b0340907102120f0703141d00c5409641c0c5170240a41c40303c01c100c045480411790754040001c0c0d695602945058014010300c0e5082c1d40e00f110a20020503a0701c5950f55030456440782041c0da8183d1240022907046901c1ca4600012000030100304002401200341d110080300c201c09900814042103603902104004120203c403c445420100041034a0b01124101d901000070700205906041680091601c2c5000810498034040e0204500845024035 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 152647985 1250 152646735 152646743
    0xe13020409090209060301050709030611120f0f1501120c0e031905060109060b19020f1014060f011e05090a08010c02061e0a0e030c0703120201060611150402010c0b04 73
    0x2102c0040550404554040c0c20100942c000e101e10303e0000d10280124280d880000c1c40e00d59241c804a001e0410441560703840c107040b00340070040b828001c0c006e02c05a2401c0d41d05905114610300401c81841c9005007400c55020180c6840134400d0300c0c10200d20090035004c0c0401c0601c002c010000710980d80034001016070a580425144c905000c50610f01c0c43c1c514141c2201c0d95a62821100340f18044040c01500d2000d03a00141d050702c10442948100d09150b05200301051510441040f80b0000c080d503001920351295a0741003144035590f10041240300c04902c1c00c058089107005001d040d407c5141c1c810703506410b10f2424003529003078801021402d403142c0d950118031181d55a007280401d5960500c0400e8000200d405040d580c0100ba901d104a10301019091103011691105c1010034540e05200f55122480c1090a403100555a400c0895068001c800000019427a00341c001c24500c4c09400c41031204400e030f80041180c401c507520340407044500036001b603040c4900440d4001c00950322030304d004d10881c85 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 152649235 1250 152647985 152647991
    0x6050f07090e010f031e080c010b01170402100f0201021b0703060e0706050d021305030a0b06012703060b01090b040b07030f0c080a1d0409050708070509010806070e13020409 76
    0x103810041410341240c000c4000000418010412002d2003400041941d4000302609a05400f08403910040604040018520040840c40c0c0da6045d50660088070150300030f8a0320400c60480740010941681c08a4009502508002d0014030403403003a040e6640e882d410b80001860450b481d1449504034120650101c180e5001207003d10402032540121780241006400400b00c850802c41c01900900a10050040181c1d01003203401102da1203030404401003101074180d4031070300041c1c28480071384002291f40e00c0c0411810000710035460389880d001d0b84600c0c0101e110702c0c041400d41e900c00011304848000c0504120b40c1c1d84001c03a1030040d11001b8001411125421903841c100c501c2c0240c2642c0c0310310002000d01860011040210f1210030031900420318910308070158040810300100300c00c0d01c004403180c0191410000204200c0c3c0059500140d90075402192120b598990800c1000300e424018101319070822000714241c03e00514020f02c3c0c0d0603004291444660300d00002c00300b00e030010782c080d440c0b03551 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 152650485 1250 152649235 152649241
    0x30506091e042f040e010608071401090f0b0304121d0d0c030b01181104060e0f030111040f0e060d12140403020301290a08030301140f030f0f0609060610080403030906050f 75
    0x1d09417107032804040e141d070000e0244a2030f100c1c42c586ca17019588128100c00d0542d604049482e840b4140309406003402c102d08100b80c507210ba40d4180c0503002103c040782c6544080081511140c0180408800a29601c020040c0d001c500b405104c0c84001181c012114440000c401200003540401c000780a0000616062490503152010704280e506a000500c4692003c000c00d003c144d901c04061800d50100350745070500b01041c0d0700403d0061814003840c2421030310101d00414102d440725140003c891200780001c3d2552076100812102c1800160000d050000310401c0344c0115001d14685a1407074410402181041c0d540c2d00481d003551250320510a0301d040a0003400c04003074108208202600050720541c03030150070140802e94900c018050303401e00f00ca42e842c0b42c1030f40c0c0e03484101c0008080710190681c0d02050019014640e1245e07100d9018a850003208002000341c400000c4852280200400358603003650450000e0304e0102001d07005504141d04c40551801050b0706026840c0644000850009985 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 152651735 1250 152650485 152650489
    0x40501020702030d080402030a08030702031c0b0f180f0903040810150e06091503030405030307060204030317150d08090306090d1e020c1017010308040501030506091e042f 75
    0xd20745136807a045c09500c0081c000075850002d800780c01c1760351008a0a50f203441d0504e041e0315500600510207a082149105810340840a030000000848282e461402c001070703030400c0000c200c1c22001991a9413405c10001401e5540260610b038009044800790380c50b0a0310b44004034206402c5151505241d41c40748030010001c00c0e000130365402080d09609007085824400005200b00402402c4081019142c41c0c0102044e5000d000b16401000010101c0b0780d500090b18100d030117500701d07100a4001c211744601c03035213100c11007420751481041c0190585c50038025400030085950004007055030058014002c2c0d1425440400506e40141610f50041c24101e0322080d004058000004940d40581c0e4004984c103029600003801802051742200c5440440b4940038040b2031115501c643d980d01415401e00010034040400700400686801780c3e0240041ea49603c10b02c601c3c00d206481c004400207201c1c2844012540943c0c2c4c1c560081d101e400038107401e00f090852070082c41480c07207130002e2043e180f4904400e01c0c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 152652985 1250 152651735 152651743
    0x3090302062107030c0e0d03090b0714010c02071a030a0603060e0c040b010f0f081f031a01090618091104020f04090e0708190819030c020f01092f0904050102070203 72
    0x891403e20f410300402419080003000b41094480d8180607da200d0311040070140110b03001c9000d8012100071540314111400c0c4024420300e0a41541009d51074006a8440d0a10101d08001910200d40c0c012111080d01d00810460303510081440001564550707010000030a68000d00381402d01d440000e00b4503498540812003150b03090303202c95041c4035101500e5815103800001003402c00d60f290801c41003aa8550480d814400102d0104010b207810a080200400ca43c0c4404002210518500440e0070703a00c82554104a8405021f078a0386400300070f0518811034140c6e003140020610440d00e2443c01540790012600366040003500d50500040460148407148151091803050707902ea030024898285440b1400341c459615071008401140e40b20004414000361764211090720f0302c8441090202d1109140003401440d0f00d6000310014090084491000700c0d050141a405581080005140a442600d2181c0d040481c0548020000c5401102d40c03542e0b80e02500c09108138058400965107514030310400d420 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 152654235 1250 152652985 152652991
    0x207050609070e130501060b0a050c0d4e0203011505040506090f150a0914060a020d030f06030b01120b0f0705040302060901090801050403020a06060b090319030903020621 75
    0x1d0351009400300141a001e0300c20355003041110000c041c40349501e040c404e000d800260411242c0c88400240b0401c1e49922030010104c00d103010056855040744180300315100700c0c02c110440c495070700340c040c45849498210581e440211254035001035202c540c641400ea00c0010f0911021081c1d03001c0010001400c038010501030200b107a19110385020305202c0010218081c20312500d010700381040041c0d5150300c50125003c042c2440e40e002d1030b01e41040c0c210042c03d1060074000e0703000c480b80882047c4a1070034160300359001003040d60086c01e2084115403080303004090040341c4003c0d250311000c0000202d406454420302a00785d241c44600d505175282031540c040d01014292800501c002002c01c002070b540f000c1524180c1c1c0d4100c2c1d109940da012078004a40c60941504810302079441c120511040540014120300124818201442080ea95040d450a6401031140c280d0701504003d07180030998a0b003e0028001c0c1d0321134104507025a880b90041407898010001039040140e0a801c00701800e0002126998 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 152655485 1250 152654235 152654251
    0x90501050a0b03100b01020a020d0b0406061a07030f0504050604080c09070905010c030c0c0b03090d030e0105090a0f02130204062606060d020304170c010903031a03060402090a0f0501060302070506 86
    0x111072a03000b4042507a4011030f04529480740e68803106522142e10a0101000342900202400c400841d1410240700c50782090b6003c4801a20700240092062008500c035442502045034460030494540c0f010b0714003a400000500400c08204000301c0c040c3d45040c060006444040010200c85d01c0b02000d10950304005032148080c000d020b04204001c1c1e9201940812055051500b1162000070780343c0152040c1950300303c490b40403004000c000c0707590030008142035580301664050180089154255088503001d03211410150081400a00071074040c6c0e0f60391020500c041c213070300c005c11140b00d008070407038007c0d4100b10002032040f580f40d001030890007003080c0311080c1c07403d00114605110b0006603141c451082c00012140c0c01000141c1840300c010782c2c2e8201c64030f0240c041580d40050161290080c4008981200440e15080482d0f05100b10150f1000c001200038000340400c3e211502000a81000100342410943e00c4140c00c2c0c05481450144e54001d140d80d440150315609a403801034100980144000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 152656735 1250 152655485 152655491
    0x50f100612020607080c0a050d0f020d1106130201021002041710020f03130201180e0106090830040f0e0f010e060306150109050306190e0303040b06011d0310090501050a 74
    0x700c05607580e042110a038503842a0b07000d42d60252955124140840d0070800f03800d6000e81c010864000e41c028002210180311130303007030721594011407600795446940c014043c04540d002c2d20000c0c0040141c0c100462001d0300500465600c00501c0c0114001e0707038429045601050740322824608000020000d034244204125019810601c3c0701e15160040d00005106030308002581c4580c00035039000e0b01c00d441c4658a0070051510090310388203417640c1c041d020310078034000a008101c00184144045204207050ba40c40013107a4245002840345440960302c2000200d010303008110009645604040c040020441d4440840c2c49181194154850341d00591003e4560340b801d404118581d6408150700d03601c011071301c039105440101800122942c00c003981013141c140c462081807001a880c01943d82c500c100d410503061000d141c0703043c05940c5a010558000700b102a80d5004600e0540c0609078206414054050001c166124000001c2c83d004080621443d040d694951410611400703001e0154030102800f814 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 152657985 1250 152656735 152656769
    0xb070c150206040f080708131403120405060a1404060e03010b04020307170705130e16090e0403050304060f090f02041b0c0303050907240e01030605010903080702030703050f1006 78
    0x194680b007004100400c00c901208107401040401010b5a0030300e0740002140c0d464055a41070303259809110b020f640d04528180302a4421403034001001c0f040720300500301c2e043c181032906050080603003040142e1024400202c02160380114804094402002117980b2044082c0c1044181403c40e42c0301e00100f40541d00402c1000360003a00b0101044456650043c0041075643c2c10104480d903010f0506010101030134a1000158204d0380c0782218001c00007140300e034607400c00d620019901c4440c0d501c5451480344e000340000303000c41c2c0031713602442c1c0c400c1c0160f4001c607841c0b64400100003101c844600880f41801ca4680820560605105081c61800d109000c01c02c0328091800240841841c80801810551038400007201c261013440b50100038410070201c0e9154504403100344002d03c05c48400c0f038001a6071601381000c158407900803071084a80c11f0b12401c0c00300381107890f016116841640d040e078143c0300c1d4403c0000000c1b002c0224441020401003c0c3c0389104200c56203405407040e0b5400064684008041 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 152659235 1250 152657985 152657987
    0xb0304020a06110a14160806010e070c080408032a0f030301140d0209040f1a06010906050c150f15040207020f040e0703051203010e01080a110405150a0b070c15 70
    0x303080075190541003504400e00c03601c0c00903107444c05420b00240096141c0e0104080c403540080c0c45250b081500e0211100b03951100c8499645a00c00d102d006c2d1312001c89004641824061044d0041e400d00641c0b42d036103850748941520703103554442d0030900c9455020010300e0b03d000944444030480d1a0788000500082080407400555a00041c003611a50448034504e0707001d1a51401d41040c402507016101c81003c0c07070241002e4a400007214070540341d510b4580c601c0004c400d421020a4440c1c00c05841e013540c1d4034241081140c45030800d201c031030a07074415400103040e000c24a201440c807412113003042d5030b80c1c5d2a184408010007644030b69110b020b54010700603140140c0d200081c0307001d158005d950001d40e10300c1b60b010203403a281d000c1d071025080e405140d182d0321261103a14000c4d03050b501400f030010440d036640c5440381d03030b200c083c0c04000d0000c014440be140340038a010303080650070281c42e400c0042002c60160015421510a92060305c05020006810041006850240c401444080780c808840140030380 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 152660485 1250 152659235 152659249
    0xf060f0f04020d0b041a04180b0408070206040801020c070503070b070b010b07021f030506100e0607020d060f020f07020406060c080f030717041a0108030c0d14091807090b030402 78
    0x12031072055402003442503442045a0164a041000800c2400710300140d070403040d03200090180090045040c80100c0d0710142e041d007a400761382c66000100201580d220388803d80160000c0101302c3e07000b241008005098403090000d801c0c081c917003c2c05892540d2600d0105031900f1000d80c00103e80f4002400324002280044803024111401c203a4115583d0340203100003261403e40c4503441c00a207204a0b000041d591b415840b941c030400003603032502d4402c03400743c90907a980001c0c0d203e40b5500400401014006003800344214000c244640c00204040d140f07a46010143e1300070350b01c4013415180c003007401c00a625103800750200030700d03450520f00c0f08004140c8607071242d0b203e41003c0706030b03910000001c40c4c0c0b040e2042e540b038559400b0210075824103040a03c0c043c19a025164030140b4101c4562002040211005c000c440192100b1402401d140d811004192440e0440000451141038240720b521955211041e080440040309805c5118031310341107601800c54960f0760420303150440e09104000050720303449 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 152661735 1250 152660485 152660509
    0x3200102071805100504050108071e15210507050d060e0f070c05030412060504050c1503130f0f080c16150c06180503130518010302040c0c0c0605030f060f 68
    0x1c100803c1c1d903a1100544403031940e40d03034811500a8035080001400b6500403c103030003690b01c103110352111701c8038460300d29a00d501c0354051601039002c5003034500781e020b006110b4180228107003a20002c05d42404801e80c01100e100b160840f0208400086850f00c2c1c0c822481035070090328440f0954030340750a0031113241007041002040807090190501c0d80b1400e110040081e140100701007c140c0380b41e002c1e00c0c500140074100c00d990403111440b940070500a980381400102c5002c401d07907a1400e045948000e00c8030b61038510382100f40c40c460050100080490b04010321903201d07500558500d5500d04200c042c85142c004500d03c441c1040519a0302401840300012031101903d2091078100150151814008001e04079a01031004150000408004000012000d002d035210880c046a030301302e940f10b0521043c043c401c0d0001599500110040c401071034240c1c823061107000c1c2c0340313010f2403075402a655442d00c500d5030b0b812120200b8000b00c10080c40381c0480800f254480420385405590082401c04200413005038 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 152662985 1250 152661735 152661779
    0x9010305120304080f0f0d060608060904060b0f06030a0c110703030206061005090d0c03060e03070807060906060b0a020c0f10120c02010213060c12081003120212040320010207 77
    0x110f010720141d64141c3c1e1050700c140300400c0e51140050b110307900340d9110120600c0c50505003140000c0c0f182c040c01c4054030502010380300c01e0340c50380c440d503400b001041d20f40d050f25840310000e0403034106500c5560186108003418080060b50034440701e805419004001d144130115442101c06000103540072907030713582000c0182c40c0e0746000400c51000762180d001d02c5c04035580108200040307030148080040303c04100c1e4001e41e070404c111481070315540d8603885200700183c1042d000300130607030020300706620420f5094060400040c8681e20f031503014250b580001c1e035420040c0c0c44290f121f83d19240101d5659840306040340d80340034041103880064810b03c202c0a080301b01c1981e803810b2650b070364000e404548401400d050207203403581d03e85801038100c00a011041c0c486905105183e04205c2c09100403a0141140180a1010b0740c80d60390340941140701503c0354821406006800140c0901c20b0000d44091441403200c542d2820301c0c03040c1d000c402040da0710114115802a030080042003201c0c0744249008400c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 152664235 1250 152662985 152662987
    0x60d02091c0807020910060f0e03010f0c0504080d0f080c0a0903050304180e06010602070b0304030212040306141e0109180b040302030c1b0604061209060603080301140901030512 78
    0x1600006205169100324550300030722141d42010822040c2c0004102c2d0314401c0745c04c1a4540c40e070501005401c03450307002c0e00c4081518031214451060040c044541d190900800102c1c03015542c061400550740d03a030f401d00c408180081004e0000d44024032a0340c1e841400351030680600ea0031000d00600642c009400340d80c80c4400010041000c6104142100c05550042c040341e070748558425021040d068154200c400081c541010000303c0200414120304031007065000300340705070402c00361a07141d50002c0c104a081d4400c0e04110f41280180c0405040114010200001e480e0001a84100e224000030a540c1490100104d130101400020b0003050640b021518001000b03082051507044071020746001a02d0881d012080004160340007009040c0f140d038810039192010510307602048095004d501840c3d0200090100344003603442440c80910720b5155503000b040100c07203501c40c8821584203410568000d0740000051002041103100c81c900c456060b03500d12004e40c50b40e143c1c9912400000c040b8003907000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 152665485 1250 152664235 152664247
    0x130f03050f010908091318120221042c040302010b18060d061d0105090c1503010b0301090b060f070f1b0e062e09140904050d081902070303060302041a060d02 69
    0x6c281d92201451589000c0c0d20082c0051030f04003800b401c54515a03880042c40f404105c2c00c202c900c00c03040350b0720400e2404038441c1003608009404011400314900383d0f0f40e41c11211290700c6441c1c0c00b04400c0d07010f540a500005140324144090002101c680329a05c42c540304a202881210349070f10069405240e00a040000c4140140d540c00248907840030228400b50f00301828000324071400714400e0510002200c035030424000d002d40c0020940401d02c52080c4000060004000103902c039000300801d108002d00e06803a06507090740010007504880c9082d036500041e41400810000781ca082c2c40140b90f141d01112088502c1c00c1c03c0580305c03030401000360b40181e9001c900c0810720007004c0c24007d003e0500440c90704c98040c00c2c040040c1054140c1c0300e00d40035405245034a1000381818400140510340000260941083c0040191461040036000801d124210390f03041410340c80314405000701ca4429a0f02183e058594010801070310302c1c001c800c000d809071440703000e20359940d1413080384d404080e0501d016031620 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 152666735 1250 152665485 152665519
    0x7091b0c110d030503100503070303021e0a020a091401050a050a050d05010204031a040c060c03051803100e100608010212010302010807030e01050411100207050a1a130f03050f01090809 81
    0x340581e4003540c1040c8808070362402c1540080c007540c880c054210070803681564030001c150396465240300c05005a004284c41c250f4100d074800c010000c6200510450f11149020303400f10301152295403100d5500340c0c0d1850030040f007118241100380100400ca5110f01010306180002e0f6a5038014411903105488014500b01040000c2d01550020b40d00080910410044038001003500842250211620b40e14000c0114999000b40f010002d4940c056a80741e0400082c070f821035510b1105803040350b50501c1046061700b6803c200340115001d9108440c041c1908002550f103032815070b045a003200d07103203134010300010084000d844c542d01e044940901c0e0206040d25180b100754001d20f1800c2501c4a00c0d428a4100418001c4001990300143c100f07445400200f148214120703224491800b0300360f0b0000440c0803c00c0340803c3c2c0b040707003c042516682860b141240300d0700c0034a04051298851220506203013006c1041c010240700f00e107083e0401e02c2c007e102c007a0b00c0e41e48031041317480381d401507a10607c0301081c030400307031 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 152667985 1250 152666735 152666753
    0x9080f0c010b0603040305070312020a0c080906070501090809100e090403180306090b04020f0d1a060102010f050f071707140a110a1a130b06042310050307091b0c 71
    0x10701c000f80c40c450340e07404c0904006180350710002c41980410840c8640c0380c44c1c0e003040c0c801c88906030300300d564001d18000306548030341255001490f400d900440511181c0080390003032295440c42481030b4082960790110409008185041307035140402d00081d01695480e43c2c43c1e4480b0290320682c03501e0b00e2041c4104140f40b21000c022079400140645142040103000c00c480c10500741d000314003c8482c641d40071443c004100903c1c07030a05000344a100741a803001403c2c0814045141c00c10014000851103806000000d0704680c030071900d22150030b91000c24000b031541c00070402e013040e44000802900c58508450003806100000308083d0761300e080010504d0301c040c410b40d226182c1c0d826410650707464610b981000c40c1c8540d40150641d03016480500414100f1455440c40d51000d98402c0030408159540030402c0000d040a0955615003040303003c8194a04160704402441003280007403445a1071b0900707042c1850701043d50080ca1a01d40340c882c0d0610140000520b0b400001014176008032450b10034500f00c054 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 152669235 1250 152667985 152668001
    0x3705042d08030d05010303030b0f060702090601020705150315010c030207120c0906031101020601050102030408100f022214030c010c1202120a0e030c0a03260c0d08060108060409080f0c01 82
    0xd01000c503c107400d0440641081d81241d009580a2082986105c10004020350000c0c005e940304900f0881c030f10060900c18207182c2e004c02c050040d901481da480f0301082c00b19035410407441441d540041040707002c0800303900341c801d031920030f18000c0314000380303035030040c0d52a5854080c4080310a001c07000c00041000911000b40a0000064144001a80c07854282c454005c100f040d10b016010b0a00046119403002040d581114407500040841c80c540304201030050003525040c94400c3d40800c8002d00c484079100d86410200c0300905103200c83ea24054841099540880c01c49100781c0103001c06845a80c1e003c00b40c0c428840d040221043d141c820b12000342c0c603088005080d44044440443c2c0c820035680c003d4200a846072050b410b440303440c1c26050400c5020130250000030710254003400940501003000c60030100c5141c101154515124602407a01d1514404090240000d00303182c08005031075a10401c0250460b40944040c0000d50413952003c02a00400c0304424020750301140c1104034071425000410 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 152670485 1250 152669235 152669249
    0x8070510020315030c0a091509110c072306031f08011b030504120c0206040b0f07170903100b01092102090c0316030c03023705042d 58
    0x344860312500303500081d400c11156440040c020000b040c81c07038100441e4000c943c0e03000034107060a040c1040d0b600001000400c0a10b400602c18444c0880c07019543e100c0c9040e21856080320316100c80641306000c2c5094440c1d045861060440302d102d4004503102a501e41029208454494503940c0b020100604c0c11503600e044003840c80480750024041206500c224a600d19554104450a680d04425402c0d980140d50082ca501c0340c0b1524021007611514841140900c020030b03c6142a40c0c951060420b81c00007650f580501078009450301c01c01c603003020a5100112011821424549040c0000f9200e044103102140041d480e8480312000341e03c6030703003610007800140c02ca0940000c014200d1401c40032111904034011011500400c0080c0b0950060f40c2c800c40f0101031406030305c24174400841c0a0102d1648400615400f80640d103001c0058448441000040250400d0060384584441c0310099800c11001c1c14840c1c00c20091101984281450031010304402181108031070014060901c405541c1c4151 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 152671735 1250 152670485 152670493
    0xb091606030c260103050105090c0f04051506180102010f0e15070516050f060703050f040f02012a1505160318080a120c0305010b0a080702010b12010f0e0303010b07020904080705 78
    0x207001ca501d400641c3e81070700c0c007410081110b99241031110f6038907240c1590840c4d000005540101c81c1d031a2540081e50710402c110400f610098121010507120b0f0044000401c0d00b81100100d0344040d40d0905c1411030280600c01c06100502d082e19480d0307181d10707802400c40a202c5541000a40d00ea008a040364820b51000076440740c5030501d414013903180d100907144045075000e590081880039220f4020315000301e00c0c8107032582d620b07110b560342c080c060b04030207001724140032503801203844c800038000148034120f6060345030100120b00b070300c0c0c8054089c07003480b00c90704920702d054207001542001800740d00083c0c01324140002d800b0000c901c04840a01002c40c0185980800175405e00c44660002c1107040d415001e1105001000d0068410b40580d102400703280d849400038464190b0040c03191101c10340041c618000000d4084c907000101e00d0444045120f8100ca80d140d0001c103a03a440035115884030004003502031801c40d410031981540342c1c0305601c0042c0c0700301014008281440045c1c07044840c00c50b8490701300c5d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 152672985 1250 152671735 152671787
    0x71206151502010207200603161103120103022106060d060b03030403030e0a080f0c06070305120403081806010806070e01050c03040e01050f10082703040f030b091606030c 75
    0x90103175014903c01c45006101c1c00100f0529040d0424000c94200010300030b50940c0d0b12158010b001e2045900e8480400192031900203054109200504200b480c1c200300005035030540c0148600505040c10250300b981125601c0d0000910205890380c008034101d800800090031828038001030803c6955150345808001000800c054200b500800461000d664001c402662411560707101c1200982400c0c0780d8008182c500514070341080200f145606c00e04005082c86488807030890710081c212002c60203d2100d80600c10066010f160b968081007055000745001e41c1845030303242d10340802515030b03000d00010102d40001e43c1e00a40690b0824400482201d03100d6544641361500c10400703104643c010003c0c603a1050941c28404071040c0300f83c0d80c03030b203a004040e1070380c03000c9082c0050b95401114a00a540000700240201407004100034107121004c0504036055090032101240d02800c0b0340c2c0355910094aa20210320010169002c440c51803c2c00210400c400070151201201c022103580d88150300c1c210 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 152674235 1250 152672985 152672987
    0xc040608030c070f0602030d05070c061506020c0607030918140c0306100507020105180307050406090b1908100903050f030901090308070813021306270e0712061515 72
    0x2800c4441d010400703c0f900184d0341c49694070180b6003401a000140c00c100301c2100c00e021541c020b2a04080c2a00d40f0803001001034407402c08650300130002d40c030040351950040004e644d041100c841c207440c00301c640750f02c3c0441d56a40a400d1100c00e00c501440d41010055680b8070b0544c561021800170600444040c0500d8040ea042c0c2d25540b0440e50148202051220044010722480c1070301c1c110350b41130b11810300d03080180c0603000142c2070354121180c1c1486052800b00b401d8841e401102c0c014014104081400f20880d0200050710102d03200b01200038107200002c00852800088600340c0c260182030000b41c182c220300301280d95114800d0f54026180001041c0b01381140e05610002015000f5541d4100780d0701c2c2e00d0021039071440c00b5640c0280d01c0310040c0341c45c0050b24007030101e9440d000d41c2e0080015801c2d07460400b0a44000c04030980c1d003100c3e204000c40f0040d40085d009840f01240301b00003412805040c045000c101124106c0060500e55640043c0e000d65000d5069050140403040c00b440d61480642074 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 152675485 1250 152674235 152674237
    0x151006080c1b0a03020d0c0c0b09030a0203070603020702090603010c0801050112090c0e070f0e010f0521070306030c1202091302010c0c030506190908040605070804172a03060601110c04060803 84
    0x210441c0107109507000030013000c1c0300d03000c050324540c0d1000ea4801223030720b042003414143d04010307480f5a00d800340c0c81040d001a5010002d6600400c40c6890140c0c88001d280104807540c03d0041010380240d040c80c07440c0741015884008903064135401d0030031958985160302400c0c01040740c020024004064072501082948180034518414400313030707503205002ea041e10700c11100c1c4054444031034046040c512060815501440250204031210001101c0605065031056a071803400d480074030209075a00010b0003070119040d500b401410140901c48181810303640420070488009108032582c01403c804a8116803040150b841c5441e0001400c0b00c0c1c0e5500c030300f001c40d1244030655011110350003500a10821001c0b0340104040c207504908880e0410349444020307140c0760b202c0d02d8120303458442080003184104190103000406082c10f001040aa52800309500b907000d00ea500384003d662a140841d0250b6070006140c41e400300e001e19048041d407001040d0380e8984403200795095072050420b600400d0141d0000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 152676735 1250 152675485 152675503
    0x213090b0f1503130c0b09010306080f0d08040c080a0b0a06050315010e04031b0f0c0f23060412060219050c06010e060d080f0a02151006080c1b 63
    0x400000c260242000754011900110035002248050b20400754048000035690025aa00d1007080c89002e6580c0c0e0340c1003101603040400880008194107440f0350b40340c0308540240c40b41400501091044911107941c07402512501c0c4d0800817208001740030030620850f500001c2c102c010855140d241146020088200c0859403c2c121070714005000030580340c00200c0c018802105440b080342a42442500d603002000204142c0c01e00c00300c2c13199407600300400004040f800b8000c0522002c0403e00d4038040f403007074100c0d070b001070180a110201030000861304001071035a44442c80c190300080b1203000101c2c501d4080c95110030013201c01b11604034248203003034004041a03003080c0700e505807010040b10150784a00841d50b0500f125807042c4014031040484400d8503800603001014182d844945da5a003010b2603011400502600f074010428203e150b80400840445020500c1f0503815413130b008100c2d141180c0940f180604004905012490741e044040c11038103003101c050b0480d98041084010140d0f9623a01e0f13 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 152677985 1250 152676735 152676749
    0x20301080c09330a03050a03180605091e0d021309142803030908030103030f02010b030d1b030918020702150c070909020102100e070609060c0b01050d0807060213 71
    0xe0300056918120b007004a030380546507400c00a1050040f01e21200d040003102c0c85030341c116401c0c544c0400420000c11103211040c0c829500c00c031041010161404011803e9401001840003d01003034115075501d144400168071420914000803641000041d414034600401039040325100913141da80000c2ca820048007140030308100c07050050224443d40d42d4081c050b200c0d400700040401c41d04803084002e040800c2140c02454007140017920381d1503049107940280d004030013280d2000e112220043d028040d205014030101c016081005800c0006006200d40c510403034100a06403030141c003094090000304015219040090440c4021403c0075002507000410580c452060b240c0c0003410024a4001c8400034060a8054813080c5d00e00402d80c0003404482034201d06500540c880580010070500ca60f89900d841a80180240342c0b4000c0090008200d5820040c2042003c03010540480c200508140c1100c00980d01a1940341d60360030507005034041c00340018646800041d0010208001c0e4403c513082e01c3d54 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 152679235 1250 152677985 152677999
    0xc09120610030f02030f0f0a0b01060804030c060e030c01061401020c0a0f12020d0b24030d0507080a0507080708030f010906081b03030903071e05010906170603010f020301080c 77
    0x600103651003004072114640088010780c103000098150503500c2a55201804981480c1120034000782021a000e0f141c0d48a544000880d0050011035180c0c0b82c0140800e040c070a0719802e064070014951040360001520082d22890300c90302e401400c00850340f104601c2c400820207a900d0b03a4001065803c41c3c1c14890052288400035800da20b080c074842004c51f442c4c02161a051450003c0381144203454400590b8008000c55522020481030311020b880740a00b1022020755001640c109248852603243c03060195200f02340e0071590300e400a04542c181c40e04100083d441d00c802c040115044e100d51a4020085940801e0714810001c042c00514007400b0000854600d9030380300c64605085900c28410b440c20707984400616020b00145083c01f1740c0701038018064919141c54840800d103098165841801c1452401031103600c6c003041c2c0d246540140c03009180c0300d0f441900c1c10030005c284e10132400c40c6c101c45420035004200d069600b58403440050000820170b54581d0b079212200c80d00c501c4541d1103540203040b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 152680485 1250 152679235 152679259
    0x6030a12022e1508190204060b0f0702090a020f070308040c0807060c06050f0c070602090a050603130510020304050327031606020d020a0c090b0a090501090c0f091d0703020d050c09 79
    0x205090410b0544d8941c400800c1e4000e828101c030700c000800220266002960b800340030816424500041c440c041110710225034a080a1042c020035000052031032280320710500c0035050303203c01d4030201c83d005505450941c059440f1030406468014059025100720711800d03100007002d54018251404c8103018440c02c0140b5901c0744101d02c1402e10844a030b8900c60703010400c480005941c0c1c1d001e404200030290041c1d243d1911103010a1180e4425106d0002e00040f915a1008010b0100003a400012003484251708505142d134995540307004801101c20f04541c0380180c0200c0601c8880c10030000500141104c62041a8403900c0c020014240a52801400380040180c0071500000b0150ba12035401280713521950310300740c0e6010040c850101c400c0d610940b044c0e00066401000e0180901909002800061410607220040c080c01d4510005000780600018100000250803c020154110000c07003c551030ba1880f0b0100d00034425241e000c40254540b1080c0b25008580c0f40150403a85429911194401 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 152681735 1250 152680485 152680511
    0x20c10050f071b0e10061404090c030b0a0906080f0307080f09031014160c03080408030c040308070c05010e01090e0601120f09050a1106250201050403050a050c01030609020306030a12022e 82
    0xb0340c807400142d420307008c010800c080c038025400041a0308040ca4000382c600d4084001440340d0303e06600c40c28103c1e031505028003003040240490005644030702d0081d8509005565030b0034a5006e003040c0300106101c08605c034140b58070306001041c80030400e00e004000c0b900c0000038840c01c00c003081c2c55459030b1100031904d0b861064000d000309055560140c4510b0090f43d22545c8400741030f4001002401c0c86a014000080002c030403801602c00c1c6c601c158003140400c1c0c241070005203940403460400b4100183c800d000c02c583c40465828680100c82032034542c05007070200b0810350140c0001c9803440c814a2404070003c003805804182c08030442c0c4207480c082c520840e903000b0031616014152110001d860012002480a0245912403034582c2c41030401d941007075907070745800381041d00403401620580c020780791b442019a810b105120282810060460840c1805001f19a0350f03000740d080144843c0000c202000130754001c00c000d001807a0300140340181c0b026180545660032148140c1c103143da40c18005000b8601c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 152682985 1250 152681735 152681747
    0x402040b031f0501080f150316030501020d1109180411060409051009020307090509040c0f03081903140703020d0f0c030b0f0a03050a240f0606020c10050f071b0e1006 73
    0xb0038490382ea506c00d0ba19034074a00656501e071200240c0d032522414a1480d00d80d00e0386404400154002c3c000140c90743c600f00e1a200039509400c80b12800380c1c004101d842d500d5540e2074002c5821100c0401c0490b031f80d81d40d80c0b4240b654400b05c0e40e1560340c0300c0d802042c0003030b090807545c0002d441800700301d4401e00c126a5038850407003070b4041a03e250001c03e10301c90b0140800e00380001002c1c0d10901078288a0442c50361440c958400008541090b1040301c0d00240040a60440000c401c0c500f003003c1c40c1c01c203e000301030500e5210010001e8400820542c0000d506029951340b5001410441d1502c5010000310744010006401004400100d60081e0849213495441d80340c00c942410880f900314014080140380c1d0303540d01c00359442c960215020b00e4440c2004500c501450f2195840440703100c0720000d09035080950103072408a10000082c0700c2c802d40d0381c81c0082180c1c40010360323141c1c84103091910789030700b8a4680080c564401000e103800903042403500052411641d800c441c00f8000c1a102d4092543d1600030031181c03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 152684235 1250 152682985 152682991
    0x30c030504170a20030703080c090607030e040b03010c030e0c1e01080402060f0703031d0303071e0309020603040c0501091715040c030f0b06010906030204050d08090402040b031f050108 81
    0x525103040807807444020321009000c0030340c0b1840d11200f0b10070050310305142e403ca01151604c031035002059800426401518190300035201103000d9041c0301a100010b0018850054018100b044034000080d4a80392500814400302e0014028080180070080041c020090100d07155420f21880004100034103041c9801041403075079404206803415480015203c40c180074000300e03000340c002c0054814072110407000d041168801e60300450710400c0c00d000055909042c078080d20030b6420400c14005942e07080050404449030507024032801c4850210b09500070b060880d8041d400890000403c001c01001d134410702c09a4000740c030342490341a10380a42c0d10710340390180845202c65001150100d0030b0302c1d030380c000940e00c07500c541f1303207004065203e603500042290904422160480700760244042c66820502c41c0014007440d1904505051400d00011089103160748094215040010000c01e151201c4e0110340141c901d04201c070741d5a0038140300b22003841050200d00c414803a0301c4200894103611500310940 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 152685485 1250 152684235 152684243
    0x150a0f02280f11090405010204080105010b0c0a06050403110106030308010f14030303040f060b100c061b0207121505070503010801060605071a0a0b15090a15080711120d020703030c030504 82
    0xc5204510395030a41081c1c0304140c15121504001d43c05107842d03641d0425a441244984000f6131100c1ca068131107403d465040e00320310f250441c01c4c80038003c181d00000d04c250381d494114002268940340d07414184c0b00c011194015551a50074130901005058103d400c09040300d0405090a90440d5034100c01c01d407000c0b44411641d45500100f0225010513000d810340c50346617005281c0050028800310000380341c80340c2c029841000c10b60f48001070302808114402c043310361003404905001c00122030402502c1d1070890140304403000c03610f45182c050043c0c0381641036111610100420503030609d0103000e8020f80091041942640c00c28001080c82032207801a544401c0c0c1c0001c01b80c1c0c0240303130081c144000c444c3c01030503109125a00d407030313030f14851b42d80e454800080d510004034142d4607104003060003204003d5400c2407103a05580c03900c01d040c8903401060b030380d44a2400c2c60902c00b4402c51300c40c8641009603007044840240004108054401ca05900a28220740320b0b480401c035010760b0000a4040c1c0707038100d030054 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 152686735 1250 152685485 152685553
    0x1501020c06092d030a200d050d0c03020c0d0f050709140106052d03010609090e0a030e03100e0d081806041704030816170c100b150a0f02 60
    0x10602400d0382c543c268000d035602400400100ea401d000c030f89003051005e030a80d24000b04071111000307480b4881d00d840304101c080c0e5800a46d10030300e8031000d558030380ba10384950401c03c40b40e1713102040c180300f880303004034222008000582004282c03c2041c0b03841c0c00244103031914041c1c20b900142c401014840c424004000410003600c0c0da00c1d001d0169040d0700320940c04102c18000314606020020044a00c142c1d401c01e09401075201d50428030f004009120315007101070481d1408805100012002840526a5906150803210b4500e4400400d0410f07120421030b15000c1d0900404002e0500c010890000c50521969001200e0f510821810180760854211040b685c1001d000314000c20b401e1122000d00006800015140603629560545150f0096907605e02d0070451003c404104841c0320354640b904104c021030710341400440038000d6100c0c000c592611885030390f520141c034803544481148400c614010940c254844119900c0035040307600d0304440400500400342c507004298010310010118181c1a6112 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 152687985 1250 152686735 152686759
    0x103050f0a03020a110117091c02010b0d061104030c0806011d0720010617031b070305031204050c100201150623030a1107030903110f0f06090a09051501020c0609 71
    0xc000a085041724104040203004204580b11042e0b43c80c0942030307203001010154840c40040e252034003584040821a41404143c9409565200300800e40b590030810010301d10103100840102881340754001008041c0b5640c0000b5210800f2480d07078101c40c1100701c404550b131880401c2080c4150221000404a03c2200211400c41c200e00d10710049e40ca0070000014000b9166040180305c80a010800314507a80009107214807103000340381e814492403500c801011614103650343e043c1c0380c1c0502800e44035025109800036062080070098032550007000380c200201808480d030020b018145151180c3c0800c80400e400007809031240c88410000b980c50007001821000034038440d88554409403504103129180c0c519441e0412070342c001031040c14425126581c03e80e10794a8004511810841110722078220a21a01c45075201c0d124010445102140d446a5480c00080003d0058519070880c0c0300040c03420b41044102d25450702e114851a409030215040134010f4402c02c0080e210765031030300d83c1080300580300b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 152689235 1250 152687985 152687993
    0x60f030a0b0111030d060302010e09010b0307050304030207030807060501030605060a03080406120207121106010e01050307150c2003100603050a02060313050d081b0325090317030103050f0a03020a 86
    0x2200510301c00515000070f040301044501d80c03079a0000c40d0f0050700560341d40d50401c00c642c0c00c4a01c0301c0f10807006a80c00c2034250303d4146800700718000101194140480040040c08061082c881c0c0f41c0a1680140d01913116103d80c2000d2000305000d001c00c071406132400c0702060041c502062080b04807a0b1143d80e1501c1c09007000000c0f030b8020b007904001309415809000001c000f410400c0f080140d0000b03660f4482103e020403604074901441a40328580125001d0b0051001d42c4010170500181d070001a45440c106010b040129410a14540302410b10820003042c1104403000c03415003506503104034100da4240707280c82c404500300c0c1d00c3d40c400100b1641c08201d0704001402c0110156501100c20f116070510704c0313266200c0c6400c0c0714940c40542d0000b0720300700c100050091156504041c0680c40e00207581103113001c1c440000356500600034150260380090520000354400d036040320243d039002c41c03c1c1d041075004803100e07012a0402e000032240c41c0141111155084000a0418006500350b40101a11081912 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 152690485 1250 152689235 152689241
    0xa03031a040e2113090b0906060c0c06032509051f0c151b050a08010f0b0a20011503050601050409170a02150906061216060509040b04110a02010605060f030a 69
    0x34004054000601c07280070311382443c07080c0310002c000d110808074480c4400010440c80070300060400d0f1084000303110507038804500062990f408401511010b90701d40381c4028038010100750000c0c4003004510b0000c0c10034000d9104600b0700c100d81059440790324880c10394800b0a50802805128000100304405000c0400d50744117540e04140707420740c00013a000500450031521200d2004900d00811800201004581d03400400c40d4010a1600b815030740d840d00f000c1102c84148240700500c0d041000a410130380b29214022201255100f02c900208100c0b145401041c040c41b600d03100503101c1e40100e400010b0700382402c7c00340340c01490b40141900402c0e820340c42000455040f40e00400214454a014100700c04200d1100b1400760104400400542c5041d00030041c1041c0c5000c50301d06190070054540340043c1000901c04255952400e2407901d0b40c2c004404038004010f13610640d86c0c401e0500701e50a100d40c80c0d00004080307041c1030381d009001064580080c450030703200f00c15011000000c1080002c0c83c100e5154 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 152691735 1250 152690485 152690533
    0x1a01050f0d0906090f0c0e0a1e0c0306080613150606051c0e0724090302010509040f18030801081e030a0516060f0b10171b07050a03031a040e 62
    0x1640026650166281c907540740d41000c40499101e110303d101442809800c4480d40e9120401c014203001e035880403041180303009d00c8082c00750025a21143c0000d00c540c040d810280c0505031250444025103080b480c01c0c130020341d4000c41550394016210380308060309094012042610380c0b0f40c5503580741141d400011500c280c1c25400b440f080c036a60b02c21140700c042e02030021000400c0d00301c90024000c00070304c494540c010000340c507aa081c40100b000400040c2d8102e02034806844080303a000403048200c15400016080b4041c81d071200c03085120410040640200ca500d05071800c00313084480302c00b0000304040c0c410091040d5060503038000c0c4403030b4185602c100c0082089040c0110701000c01714540e50f6801c183c58401081911064580403d0b10301d03030504a010b410021424503008400e40101c65100c00c4c0d00da8040c048104100100c0301150090240d401112080e5030f000d0f04170ba00d4429142402401802c15640003800400190a00f42c80ca14186c0640250002d403480600001910f805d29041499422 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 152692985 1250 152691735 152691743
    0x2090a1403100f0b0f0d03020601060e041d03031012051002030a24050f060405010801030f0c0b030c030a051302060a11100608010e01050604020309061501050f07061a01050f0d09 78
    0x100b40a69410822070041144064669802003011503154082140c41c80f00b100480c2e0244018148003000300b5400148641102d1450801c4001d240c4141d000c2000340c014581403103100240740c10702c0c050b900b10000046202d080c1d42c1c40300765401d640301c6450300c54440001f01c024159174030100e10312400000c03d6000319084401c17a0030015801480c010405901c2031160b01c04d412080010208104504140c02080586841100e002d1328060405001030301200d010700005d01410780000d141c0c8100480000d031000600380d2100707800e440e8989042d2442031580b044610b40c0609041c200400c00d11680d080000426a60040c80903050203020b8808480d000100c19540e9518804c1c1c0c00c2c441001d01c940c2c89407002a01c0514000300d00000c5050449003529009841240114810001c01c003000c17201140c105d07001142c60903185480f81a00740125038074019101001c99286c030009203041005519844646001c041c1c040b4181e14181100041d45c4038003940403e2040d0550410a4501a82855021501c02442 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 152694235 1250 152692985 152692993
    0xa0b01050a0f06050a09150e120d021915050c03011a0307050909040201020106051003231003030f0e0603010f03020f0f0603070315030c0e18030a05042c040b061302090a1403 76
    0xd00d090141140c0c47c1201510041100898800300600700a0f035110905030900004000c4520712841c000d54031140c842c1408165400d15070110104851078404100d45040d4100a0206007001345038544175034001c2c030030002e550b4104c203020b02504003003105036481241c040c0c440c03d040c07640d2001441001d54004008034115561803401141e10b5945000e40350342144580e0380003444600c0701101a29010080500039848410701d407c2004a003a081e404805881e810b15204011182d038070300c103031464008400c0003540000c01000214800d0030001d00c22040300d00841d140c4c0d4071600c40400303016600c92a484800c0d00418200b0018180701d0082d04800000c0201140302d0030b1407903581c1c50b0700700654060b030404620712010005200320080c800c01c0d410411508a005546003000c6208082c1c41807140b4400d9000d03050007004400140c15407400c0960b00c0308003072000c200d401c3c6050328182c0300e04801190010302c500b0200c1002c030501580c3d8400e0341c400d5032015054408050030030709180656801d610b09103503d482 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 152695485 1250 152694235 152694239
    0x150b060702120318030a0b1609080106120c060509150c030403021302040e101203030f0207080a030c0201180503070f080702180f0a1407080405010e0307050a0b01050a0f06050a09 78
    0x94625802c444204640702941c1c80760144070582e40d140304c200c2c2819100f03500c21190034000c01c0c4464031981e0403000d556160340614442c04d000b0755060203d0340c403e030415480c000300054070048000b81280003601c04c1100154007074450340241c030b0341c1c0240d114079900300041c1c107800402c1201c418004d01012100508a0b82800d55903030018151740480d89a0307692580d00420100119402025090340228401001112517420421404150007101e003001d803c0648034800f040e80303010b01d5070448000580140185030fa414118074003a0281c44043c0039003005628020860490160041c0321032075050303000020f940b624219895110110100102c02d903030499042010500683c2c0b26803100390080080720b2150740c1c51030041d4100c1031000e03004107038840403420444503071300a51059103400e03400700e09814100c0c50f503161401c200740108101d102c4004907200010790841403010000d2030340502d9108403440f10190ba20350080c0024140903100b03020304104100300622207540a4800340c80c0c451410304c0c200c200f0315 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 152696735 1250 152695485 152695489
    0x30b0f072304120807020f090934060503070e030106080a0303020c0325030206060f01050313030c05100b090c04050a0506071104060612050916060c020111010e010b01120504150b060702 81
    0xa0f4002d034100ca8103a40051810b04504000e42511202c2008452003602c525240b4802c984620201c0da082c1d00545600c40507900d450500c00101010550217a00b4009094403004054495802562907102050482000c21860b00e01401102d00380d0f40c0c44c6014180041c05540c059011750468400364049000a201303890305018170003804c400044040415281010803400c1c044c1c10284040c080c14009d0303201441041460b6007040840303030000300356504070041881d03074101121a0303491010f008107540230b4016012407540c15a04549105501250084841d4580a03120b05691046100d89500140301150400c41d916110010304080c600451102d0011060840090101d65640c0c0000003c03540f08005d032403072040b152282c203a00a80100041c0f01c1007064401840d1064024401c880c100040c0c4030303100d8210b921400111420b02407440092103e1481401c40c10702030481880c1c120b00040b0100300d80c00910b04980100d03405190042d81c01d82010312210104409000d03110300603504036004125542c016 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 152697841 1106 152696735 152696759
    0x50607030531180902030d08180a0c0b0a0c1a01030b1305070302040e010b04050f0106170103210e03030706200a05090603040f021009030b0f072304 65
    0x4000300d0f070003502a0031401c20094050041c28010355600ea00042810b0048480354031119807041d070084010782e82c504402d0064401e080411082140e0100300380100344036010b03454445110002c40e00c5e0560500081d80698089880840040050185030700c046034004e43e80551380c4007003403610388070b8030358400c3c0700e02020b4481d6984480d8440442001d501403035900001810500003850303c0001511580340902c140da0104420035031a04000801b2820a8180c1e54004a140304107025402c400c5d0141d040c00710100188000c04041d004156810409807030b01c148100e002013041200c5004c160003000e181454114041c1d0f050181e0b09410707400a096074018102604d03010788907034590400c0b40001d651088045d4109048441c0c07580c0c0c17240e1000780032040d0790040c0c440d01c5140d105e00302d103002c440700108c6110f400107024501402c001c440d14400302a10f02c012640103401c2c10386600d125210 = true := by decide +kernel

theorem cover : BRFrame.Cov 152517985 152697841 := by
  have h0 := BRFrame.cov_init 152517985
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152517985 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 152517985 ≤ n) (h2 : n < 152697841) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
