-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1850
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:53:58.624674+00:00
-- url     : https://prove2.me/submissions/5c1b5ceb-024e-4314-b874-624cc12206fe

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 332553956 ≤ n < 332733812 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 332555206 1250 332553956 332554003
    0x316061805061806041112070b210f25050d050412020607090806010909080f0310032907030b0102011401090509010c030b0a030605131704030c050402210603 69
    0x302c0c9007442000d07100b0321007041902c1150710503a00c0c3c0d13007910094908503e00e140154242405868248100307a20401c42e41190741d02c400070348042d808a94544280300c45140c4980700c0a0701341c09802d0f0003054000c41c09066042401c20003964500303001e0005003e1200c502c950103800c0c0580281c035601c61108400f081b4510382800c1040c08400d008021200502522000401043c010640c40c0c0039600c800780144540d81c20407019400514070302c00241c62012007449080c1c00c249050004510442d00801480003040c41c61030310500035005600d40640b0044d10030320110701056105041640400301d031401140391001080181e00500d030b03510b03002c5850307800d10300045649171560700b00902420313000008006001404504078100c604000c030a560081c0c040d070702000410321f203401994201d0a00d034000c1141d078a441d40c411101d581c2c0b0050b20380751a42c01003400c00c1030140d0b02c81060004d01d4140c400f9490b0100c40308003850311100703400d1491100341080c0701080c11074030108030380c10f02d0040112802a010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 332556456 1250 332555206 332555213
    0x606031f09023417040b030c18011103070204050a0e01090317150612041106040909120302040b1e04080312010f080a08030f090c0a0605030402041d03160618 69
    0x1d501520400c1e1103000c44084560042540480080b071401c6005007016000700c240d41e828100344011240c9071144c0e04140300c0402e0b02142100118050342c640f4128554a0241c0c18203c80c84414490003181400342c000b20060039020b000c022618071a504480c005078560740c07550058010980b80e00c00c0090380d0f2801070264201600600d803650320401040700c03404c16030b55540c07000031031020840001760016814880c606034921032903001504140b2070680012820740e860042003103500130380d00c42c103d080d89640c00f08040c010520410f0b030000c01d0b145020f51400741407040c0c1c480c4c1b9115240c4081c2140200e080000401500301060b5000b80072421300707503940c070b04603100c5800100b4400c1c010a40828200d0b900000c454100040ca03181455002d038180f0309564a1109040b0010341c01060480707903000c0d12542c5509a030715440ca841c05070800d51651138603405c03d030040c130003143ca42010b544a10000c81c0c11060704500000306881440301120300781c64074117a45242000c0030700710035001148d00903ca402c3c24400c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 332557706 1250 332556456 332556461
    0x204020720040609051501050c10110703091514160203010513060501050d0b070f03110706020a020c090903040b160b0a02040501140906040e04050a02090a0b120102120606031f09 78
    0x211401c42e8103010090f2a02800c07070072a8000c1d56680400c140c510b60016640d4000c50240c500f20034282d050f585035107203045490041c4c40f00c681c0c00c1100d11800041c01c508054000043e40003816000000950781c840d04a0081d00150004040c1140c600004c1070140300e101c11104c0105a0302e40c0540240903504110707001c241c4040080c9012a00c5500340300c0086014203102e01300d49201343d0884482c45a98035913070019580c00c0e001d000154101134035110103440c508413403001407010f144190f0700107030360f29404d20009080c1403100404030b10503030300c10091189000001040d00c0584103407a04003036540761980d0454400410b4600c0c020300306030080003002071b0001c0540c060b03c1180e03005c1e03d0740c5000034041c0040f00780791303c0745150701d40e4044014001400014101c0d031019a01c10311440480d420141140c002804006080362030517071403600d41f03a00400f0790034200040d02c410804a0000c6d070510b124105041c100040040100b030144c0300100005070025810380802c150001480c122084071516100301201 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 332558956 1250 332557706 332557763
    0x91305010e0304090b0f030d050310090e0a060c0c110112020903010f0603030e0603010b0412080f0304050a031409090c0c07150f020c0603090d0e04110a020f070e0c0d0902040207 78
    0x4c002e0710300800459503043c2614400c1d0000d030000c001c0e00b000444042c080e11142c00281168803400109100401d036400503103d404403da10b810b004040700c450b940340c00030550705055200300401024841d8400040c4000908003000042400d04d07010f603012040b0020028050030b2043c3d5410360070a211510b803c0010361066040e24060b94032100b0751100b803824020980b200784284c001161007088100a0101650f03000800b1601c0361443c075240c02c10300070507401c807600181c03070541d56034002a108804150700000303a40c0f07603031901400b50b03030410f51441c001540c00d000051003005805030009882006040a00400c80900700e02c2012510f0341ca81d5040045c2541d02c207060090262080d00c02c207030100d00c1c0c00420780e03211705044001031520b580d114608490341108004001d030081d40341d1b84610900c03405d00b0050078404e0300c941e0092000c655001c2a01e45005041e505c03e22210328948203020180701102c00f15910b01ca9071045c0403400c41d0903480418001e208000000d024040f80d0180000c040d04000070750340 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 332560206 1250 332558956 332558969
    0x2090f150a030320030c0307110402041208190806060901321804110f0c0109020901090c02060f0603030301150e0406090b040b0102070e0a1104030602070302010c0f08070e091305010e0304 82
    0x2c0b9035154135019150b072480341c0c1c080200d01394010700540d0f001514480c0381440400014002505069407038085e00105440c00104488015000c20400c030707071050003544203520680a280c40c40203410000701203032080c030805401c1410040340005c40c0c5045096102d050307604c04e0440225500e01c4502c409000c005800241c981250703000040c0060300b4514013402481603901d03d62085903e0500c50700010481e07030707018031503501181d500d401c02400560346100903107008207a003500c08124041da804000707080050080804041c0b981042c01d000c4907840010549054540700501e0540d2520f0041040d03410ba1710f03c40070590f2145c01c0800128464190303411000062074151000c0c807003005500010384e2502c1e01409500002d0b509100000c0000d030071604140c42c000710306c5000c05e01c0c0c5a00c944a4200740c0e4084d0303500ba005070b0344510302019a0340d07000c0045841c0802c9440d15512074102100300516107819250503a00c00d44641d001b0514000d0700364001581c3d0b80d44500204118004903403000d840390071921965 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 332561456 1250 332560206 332560247
    0x70c0507051c02011b0201050d051f0303120e06010b0904110c030f0d0e03120c09060c030408070807120c0b09270f010f06090b0a1e050706051302090f150a0303 70
    0x71404804441c071740c91046074141c55003404c1c0b2524946000c010000202484003601c3c1420145070303041c202c500c41c5070146009035107050038420b4821022081d2022407409070308c3d9901070313401040700e0045d0300240d800580c4100e80c0881e945408444d00c0c8118041c140042c182400001115034007034030441d00a22103107442200c01d0000d100d820340c5080c0c80c1e01900e001c140c42d0796400700c005890107150000904180300014403144c01c140d61405070714910340064002c00c1c55a0700c00c2c403050095030400c0009d90010f101801c100c0f08905550380d903003c45100c1903ca50041142c0109010305103a89040b2142100c2001c074107001131000d2041c08400c11403805692900c1c03070514000020484081580c4081e042c1d61683c0c6442c18003600e450011300050b80400818020041c61800c80440302c4101c0c00b18502c8642c040d51174544480903070910340704469010701540c42200614542400603141c400d14550300041d03070151480b05940f080e040344044021183c590fa03000720081c03004800c0503008a0696031154544504 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 332562706 1250 332561456 332561477
    0x5190c0c0e04120905030606040f0e0d0503010e090706050f072d0201090602120433050c06010b1c050709170307110a0302031c09150e0423070c0507051c0201 69
    0xa90b403180c0f03107024481d0160011f400080903402c058020f0100c0c4901100f0000d04010f14410035424100ca04403c2c0d070001c0e2000004220007503410310015000407500018044492034860060302c54490b00440b000c0001001c81c0704814492403403821004401940300d01c003490075200000c0041442005012030101d0348140d070218025100041c01946440711038050780c5040e0806100f80303141c8100807011030007085da41948428640a90003584034a01003602c646468160a002c84c6023080070580029101500900c1444888010070590300003034242c4450006080d00c0740c032011161381d14941c000c2100c0004a01600c000c8100c008002e05205010b24100b26004040310104515800c0521001e5403641c450105003051141006a030440d1104038242240942d07517480f006000180502116004101a10590390700307400c00740945a8903140003088000c61a010403106424824040c14007410000c0c0c02ca440000c00c02d0800c030741806040b0040800020110072614043d8000304503030100e0005000905 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 332563956 1250 332562706 332562743
    0xc1509030d112e0e030d150f060f020a030f02031b0c0a0501080105060912033001090c0215090a0f110406080a050303040b04061404140111040605190c0c0e04 69
    0x811501003c07500c0c3d164010040b0300001c040d1080344003090301800100100302d181c0c4103a200c1d4000c0c80741c1500c80d05034020f2400c0d84512107440b266004c54140a64102003604c0d640d0f02281e500b0586d40e040c14910804481c06d43c00300e181d801010503280c001c2c4501766243d403040d000021640b0200e90102c40c106060342e100c1004540019080c4901500100180203040c92868000b0302c0c0d08841c228541164180146150401d65101911411810f03030b4400c0c01980071188080486070780505051542400700c0e2a826400a64a50307201081c0b48451380c0000210341d0084040c84402d00594100a4a26500b4914244008150210103007148903900d0190000340501c00401c50985194000c0042c6003599600c0c0c550b803210403002401240e2a6945181c0400414000480c150080c1d00454400d10780c1049010080d084804001480c000b0410030310040181503485000c5500ca444420520a0186075403002584c4500072240020024007681d24046250800a080644954082e0344800d884c3c814018 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 332565206 1250 332563956 332563993
    0x6060f050102031b0c060714060c030f0f06011101060308090a080703080403030503040206040b0313030e030c0a140310061215020415110a170c1e0c1509030d11 70
    0x104050150308180403910780b652007118101c131400d2005090329150320044000451a61100c2402c5400c50000b0041ea00d000e4420007040364003454202d0780d40d15504044904c181b903000020a0013032211080c8000401692251508110700c803d07440003071200395203902d8280b1007a00000b403014098445000b002850640001d001c4086036000600701d4a40b07810350b06c0803250b035400144141c0e0403600402c03000510039511030040d8440c80900c065203100001501d4010111981d0303000c9248254048104880c0d965200e580520846400d41d5642c42d20f4060100440c0c2401d6041d502030502d00d29080d00003501040303840754504c0052203480054144425098200c040f402980140340d0400d103a20300f0300803414040d46c03903144204001422540901c515503612085640008880012450085202c6000c0d0401308940d29940c0858014459500c00300c000f169607a400d134094543c424105c01440e0140c10301000708641d407142000c1c0960784554030306e80300030b03016092108d05030f40c407032040f0722001e42012070b5003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 332566456 1250 332565206 332565209
    0xe07030209010b1602030d08070e01080f160e03010c0c0203071d06010c0510111b0a0213110c12030f0106020607080a0b0102030d1d060105030703050a120e0d05010906060f 75
    0x40c007904003a402e2845003100e9030801c988140d18500905100d01c096a001c03c4200c0340d0816a0741e41d03001c113142c1210020203005d501290385040c45000418444824882c2c04102d6104861807490011320074aa070045a4108480420540652030203092201c0c1a41c44220004464000c0c1c049400040e0740c4c945a1b000c2c012601000000c200b40c402c00300e4150341c070589032031728054025811145505100c104483c1251485014500d503c000003910010b9100d04203d04030100031100060050501c40e0707008138400b5549000c030700019564582c0c1c000042034420b000c1d1050307c16042c0844032410508145e01c0000d0703001391001802c404d01c440000030300da44002441c0e407040d1020741e80c02d20580c80c7c0829000291458a10f11415400103100c1d400c4903540d103104405401002c3c1e5803104150030310b40302e506d04081d0182c00c03460013a0807014003031011810024411903000d0b88030240342031040c01c0103000ca4000b01402452a403103030214451000b03105054003c0804140030303010400c84569030b03141090000b1241d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 332567706 1250 332566456 332566459
    0xf0a11060c09091017010b0907030e03040b0f040f06050c010b040e1c02120a0305061309030503071b0803070201050a0f0e0d080a061205240f130c05100c060e070302 72
    0x1007103000320314105641e8840d048000c144421901d00d0b00d5000e40c43c8801000022001c20760741d41c01c5940854580b923a01e060300310b416401c08124001e10751104da61248103500030341c1d40c4280000f500301e01d500c84000441d0014034070f0341c41544926071240002082ea502c22401308a0540c00c0860020300e503e458030032000c000c0c04250003480406401442d403600e03010600402e4041d8064408408104004c0c1c0d001400c40c0421698001004c2c40e02504000c0c20703540c02c2c0640050315151200b03180c000ba800c03404407500f04145041100081480408614000381408401881500c011040c80b441e540c05400030360103000c0076013040c80702c3c00c092a0004102c500740d050803c0c082e4000509400351a02a090305608000b401402188031615031102e04001b10305c003075044503283d2040741540d01c1d03580d00804900040c41d028241815034100600383c01441940a01031540021b480c03210541007105207258080101005032804a16443e0210040c02201d40c42c2c0040d991242400641e00c03070b414001c14150140e960 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 332568956 1250 332567706 332567731
    0xc0908060c0f0d1d030313050708071d10030f0b0612010b010815060d0501060819050c07060f0e01050a050153030c0106031a13030f0507080f0a1106 65
    0x20000d2420043c2811408080031000004c66a00c1c66081c00c0c0020752040c07191844a165003c1c440ca00729160000c9603104064a4100b044103004a142480844030114060070519015489211986007000b040f0b6000400c15292581048200091408100c0c41280300710740001007020710030066800e803210302d851580010190000602c002c5548003a460000402900701401d050301040e00350102c44003a04040007007501c80c010404240c2d880454000740d074051103c140442d08003401c182642d80566038005207116100e0b030711405001d66a911205115245031300900ca1800d210030072000402e003e0007106614448152100441080d0102186a2180e01101c0c1c4000041c48032250390f045078407644040214810348504401c000040021b055242d100900020710700d8554601100c03160101c41c0000d9a82f000c801c2003040c21024164805035842e0181031400c919207603001c0496261280c02c400030301d452000704608041c442114058840c02040d80c0b60819544241d107500fa0ba03641007180c40c110000b0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 332570206 1250 332568956 332568967
    0x1d0102070618030501020c25031e0312020a09080c10050904020708040b12071812030c080f0d06230a150c1217010e010506040611100c0908060c0f 64
    0x20b10602402884001c4011441d203156142e54409003a61711025070340e5166841a01c10440c030951041202c0c01403c8040e4441181c0b603c2c0d9640e840380c00107507500c0c0348010341041d41d81c4001d042c090501ca580900500d5411981d40d0b50b9840d0160018101340201b14181c030075200d95182a00300b002108500780d50704d485182c1026604010403000c3d5204040466110720140030010700040700001800c06d005000c06128450310304800d0040c4081e101a010005c0340041c1582042926030a00180c8170240c0c1528092500344080d042c07030415803080018040320349a000403222002c00381540500243c2c1c000304169a140114450a00c1c404085920400d5010054586c1001808174646d0b84000c80e0210b4240074a9840d52a21580c8084541c0107002d004905492814103914500c8110107025140c3d030031000e8132650414020840a0140d0b0040000380006c1c0c0a1200300e041080003c0140c85500807824880c03840b507100020312250300d0b8810300845110b248089190040c80b0780544060b080041c0c070043c2041d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 332571456 1250 332570206 332570219
    0x1b061309020715110418270c0e01121403040e0712150b0705010b040c0522030b07030e1c0c110f04060f0f0530100903020106061d010207 60
    0x80d0b00c42d950482d81e86402c10340582c6850309901a80740c1da200010742c2d0545551510039080145051080c1d80340d031041c074120314581200314074104140320003004460000c414106203410707003108141e9001704400d007607034000000b0810706c0342c001503401c1c500c20b40201c40340d00c8211400c542d5078017a40c00307007048441c1c892000546182c460901c0903104602d190000c102c10386500c01c0303030520a4280d00810b01902001860702c0600c00c2c01d0044212016041c0c50070006250b000c000103010b8010301c119070080c1b9604003134207502d44a00410040245410118619150034800000740040c110b0108050040c05040102007005002c80c001d025001c116440303e8560b1420359840c0d2000c46c0c04a5030055000c2d20040402201c2c0c2c0311403042202800950418034209801c0503e564240031699220724426503081000064031007070310607030b9050480c90714204001e4906e0310a410f8100440c130140d03007000624006002c000d02d41d054001c00100d4086880d40c510345000c150f642e4a008040041d0715015030300124040105 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 332572706 1250 332571456 332571461
    0xa140c0d08190f020d060602030c060a0b030703150b01080601080705070b041a04030207030312090206040306110712090f0e160815030109050106030c14031c03020909091b061309 78
    0x456000d1602c0c01c0c4144001c0303221000c891038000d900c903020b90b02081c05d0080107800d20604000c0e1556000031030a180300d900109036034070350091645243d0f64484500000c56101002800050360344100c2035800c1004540ba07801c01000010368407400a80d0140c003003100355004a861500850303103507440d5464030001d91500408910060022290b2220b149110112100041421130281c1c0c440c0e07000c0e042c2d02e49142002801407a4800180b80007515041001e40140d9a0a040b241101d81c403070701c04945001280d0f0340301010300465501074040c4001e50084250158020030400c140d48103950444a5591140f00036024413004682d001c1c0c41840900c04420b0301030080b103046d540450040001401e104520f404203094032010201101c1981d11803c044c01005a44005c040c06010003024800c07a180d0303c24006607440903810650311810260811440783e01348079030101e601c4100007405c5010141002140c940e940c903e001e0800141c101d004201c0a094030b803100c1211008072030352014000080c00c00050000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 332573956 1250 332572706 332572711
    0x20904050c0f122d100906050a0311030111071a090a0f0609020420070c08010506181302040221090604111e0a0b0a09060c0510020708130b0a140c0d08 66
    0xc1389912090650042d00300380c03e004540340340c541c0c10340c1c0706410107407480b113407154003038002c2c1c05100d0501c2806e208030744036540c0510469410060106c0c4120700e0001084c01064a0107001b00306010000c1c101d07050000c0e10017541ea01400d03007070700440c095640c80c0c06503848104500000b0460700c80c03500c0e0100031071841d41104044500040c8001009030320031004001e2044000c000303414201000c200401030041810f140e4000b003000c2c800030712075460403400084001e40744083d0006440c030320ba4080395030b5800e14072622400039030140c0b0455483e01e100c1d8458002c1d407410642c8000186102c0000ba04011012074114003443e441808404070284401c1084800d10700314100c2c2c0f003500c1c65855548a40d0781c850801c0002842d420650990300d1400d240c0050401402e5000746051000c01920480020380c0060b848004002c0c032000140c40da2034514081030144221005603420100104020400c41d06c400700500b290040da407a051040f102307401d1000c5190240d0848802103410182c205d0000c81d000300c401e1039 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 332575206 1250 332573956 332573971
    0x40b04031101021201030303151d0610050d02040b09090601020313360b03010c090b0f031519060e010e0901030210020102070807031d181801060810020904050c0f12 72
    0x1410040d50b9490000258826407047d000640c803003820fa440d00b20052042000f03000910020310b000c81c03c80d11859240740000e01401c0c0120995014020160320540555182c2104d40d403042d5a10fa5aa0342144404e4000d0540c04d4402d01500c030118500f51b00000807210841d00740c2d65503910740c0b468040b01404192981c080002c05d00c414801c040e03011b12407405c01c4580e0040c0c04000040c4180268245400c403511580386000f8410001c1090100e0440042610042c2070900800f55481d0ba0301100e2a040103c1c060181c2e401944000070210001c003001203d03810340714a50340d002c0070708498100440e0341100c50b40c10207030003020800c0180054140910b1380408030140e800090b140882d40d59034002940c3c010b20058000400300d00000404c0e81c8a0004036042d00c40c11191880f04e09107002c0381510440380174180442c00d09035403455044084080d00181d00812000f002c0d07990950720400054040c1d84240c2010380715610f44000242c3c055080001c0d142000001030b500350408240038900d0040c07403006007002 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 332576456 1250 332575206 332575211
    0xc0c06070c05030d24050609061606090f030203030702060903040f0902030c07240501270c0e030d0e1c050303010302010807050c07090f0f050405120901050d0203090304030c060206040b04031101 85
    0xa10700c80c1403170700900000642da5400c440c01c0c01d40d00804614891800d40026210b03a004200c0c3e1040e40c0d65200a98402c4a0040000e107a140c18918080e001008140c400405560100c10300038141f680202c05103210302140c1e003d462050756403d640270380b248560701503484503251410091000c0709840e030140d50300910b0303410350510b000207945800c1031801d0040c5c40c80d906115060210544450329010b1140100028070300e03000ca501a07028540008650500c1040505965100192046215a00c800b401800c00350a0b01d400c10f4103400d00601581c65544424082d150780c502240500e0000306902001d150403202560130359003182d004554100d4080d00d200b00300201031100c0c20b44840140400402000412000900c2101d0054682d0642c1c0d003040d00c44000350715100411001c10800304001d02c950200c000c1d07040c1e0b240d034840010303209801a00c0904044510210801410000c000000d1060381e000e03010b21280d19680c4d40049a6603513084038002c000c0b02c1f8050200d0006030055403500e0101c410b10001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 332577706 1250 332576456 332576467
    0x14060705040b0703020c040603110a090506010c0209061f0302031803070503040b13080d020109020a1d01050f370509071704150c0c060f0608031c15030f06050c0c06070c0503 76
    0x941074230842c0d0000d44120102ca00a0000381c5030245007040100310f042414001403811000107041c000703000710060b00500e2008000358650b940e4105009425003200c05078155680402801802900100c503030303c08205280182166400000041d6110140d10800035231801b801d1144072045a04400c041c090b00c9141f0110210b9880c04c1070043d1107000081364000149003d441c010008444101d501043c04400403503202c1031649807504405041d039000781c0c0d6143c0e400c083c0741c02168007100418003040c00306509081d0b41000800540c115402c0c0c0c143c05080280d143c2d101c004000d4108404e130f4481001c101c0c03000d100074994101c21902c030740c011f01506080d0310401c15040d0303080c20741e010601101c0c00603c07140c600404100980c4202e66441012075000c110940c1007000203544c903c1460031020320700d4066076003900c0c031614940040759a2031480e032044109aa585c9070907450316545000c1103039507509181c0000c501d88000d6080d40d90400c5a64003c1c00213894803582580e0384244800251142e0004014 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 332578956 1250 332577706 332577709
    0x60203180f0a0503190605010506070f1103120c0601140907080103260403080d29010309020a031209060e0906101809020c070317181c0b01030f14060705040b0703020c 73
    0x4540310892018072024110705c007440d00108542c4160031640c441d000501c15007000c203402c00a00000b50782d020002c00c0403003101d440002c1c907088004040002c0d0142c001a01040000d011610078102d1780601c8600c020340c2034002c104401d0040c111281c0c0c0001e0810401040800d04400d461610070242d00700411041031a00600003803640150015500c8440010f64a041d8407020300c1000c000c02268000080d00800001648002000050140741010f480300040e1095681d035540c2c0c00c00540c0d0244001103508020017010381402c1c001d214001c046820000012507a0400000c581d1144100400d0a0313411180038109865a40c0c5500084801490003480170911003980c2c4014000d03000700b10010700b003051441c42c0281d01880341418071042d030f0070306210380104400c0401d00642080c0d0201c1c1c46410f80711038404050b502001c5880702030502d01e130920000040c49001d00c0c03a8082030f03004088401205821100c10303565070405030341210019508004c20010b0005070f001501c90380e0320034070550305003268100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 332580206 1250 332578956 332578963
    0x613080d0e0a060203062404061d1306080610030b1909050a0b180708060106080408070c0311040b061207030c03090c08070608072111040909140601060203180f0a0503 73
    0x110b080710310369030000902c01c09141c407a2000075501c07100c00390600600f0b140c0594512a014900c6101d081c00322181e050015903401c02203440d0034400c060924108440049a50f01c05401903115001d024015240440c0d10102d62030305580640703400507000c110700d80700d895101170304406030944110529666540a00003a005000c0b041045002e00103019141c00c1400004110020781e10101089901c001410031004201199650440700382d801c169005a8950916401d140300350b480c014924105180040104101c48000c001241d20581c1d0420081140c2030901800c3d1040091820f40c0e80054000030301d07c10b11980120404800380d160108500040307a4a01c0c9241c41550810002c9802848c1c084c014107522070091584003900b4984001c2c40c503200001c1c6071222500948400e41c8688460b084e144e050301c070340101d5008000c100002c05c51840301381890322807a04040c14840184c0120800050442d20000c259a400e05094000c0e0060780150030404c20a400c81e032000c660411052070f40020780799400d1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 332581456 1250 332580206 332580223
    0xf2d210314100e011403060a050405030714070f0504020c0303040f0606090903030203091903090b0a0c0b0108010c0f030605060d090c05060712111209190806090d030b030613080d0e 79
    0x2040c01076441800c00f203280c444802c050304941c1894105190149096600203465904011003400001d20b50f01e8608044d42140f19840300940910840c000c8105039800c001200d404440300c41080052030f80c0c03030784104004e13807264060108003503200b4400300d4086031601c00d03107503646481007800084d480d0340da2801200303072420414258003003a404020090b61107418410110b166101001d0303070074440d0b0700b03650140110301640a40c04c141000030400e13108007402960145070080e0040d01441080da550050107020b8001c0e04a501d0020354080c01d000d0004e4000d000c2d0b8425108001c0c241b41c10b2a80d8090a0001030a02003005c0d20b001c550007400280d00c0c0c94440040c01414003035083e50030800c400c1c0130081d1840346058442d40803035111070b030504d10850301035090300c2c2c240c07408407000c616030956452a41d0210420790008100d42c0160320510183c1c010018006180203a1a2401d000c0c218000d8100360715018100d40213181002501413650009202c0340017884101c0034664000f42c00c0510310700b0a851714403203 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 332582706 1250 332581456 332581471
    0x11030c0a090c03390201021606050124091401050702060a08040215030c04030308040201121416090f03060228050403060b030109050c090a090f2d210314 67
    0x40300a450321156140c0112006120844d40f42901158040b0300e10151100040c2090351440c480d50503035030054800c0d01281c0600c0c00c0d02c0340020084803181020301c0105028490b40a116050322840320034941502d481d548000841c0d102d0300b0314107103094600700d50842c10b032003a20304000040000d0001a500c540c00740c0b075100c080c0c0c3e50318be0042c40d01b8814803815500c1405468070307c0a0a1040200e0281c076142103070160703507151034040030640390761005031465003944ca058102e40e0300340b01040305800340c3c3c2013200c0e100d03c664103071440d14005200e81c103541d0301410b8081d086034956000400c3c0086442900103103030b82140c0c00e88248201d00d44022003080e4801c001c01c104001000014100284009400398840c0f214086000300044099039031415601d2a0b0000340a0064042400103070b0401c0c0344c0c1d4481e400b5a60003514a618000a40c43e00240880101801d00d4550060a08800c035084e62003802c424207591007240040000f940055150f10350102400c000105a2928420341d044150100b20600421f403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 332583956 1250 332582706 332582711
    0xe01030c0504150305030702130e0123060109030c030f0512040e07090608090c210316050607080402060a050f0913140714070f11030d0c05010c02060705040311030c0a09 74
    0x824081005403003c40d0f018010b0341c41d00c40e40070f10100350701204482e0b503544c1c1124190f009000f24442c0320702500d00f10301000f8195103807101100c01d0b1045507179004051a000c07103505080341d4488005540f0305586000152124410250520008150204e103c1c3c14501803030403502c2c0000a06a042d074039a0250b0001958009010244180981c001000700e01402803420155101e240450780c0c940d50b01308034440180704ac03401100001009a041c1d00418900400405803507860000c0d400080b144140c001c0c08641512541e000a24054440c100303440c0921341c014411031509220140c121000d4000d400040022038041103107440d140d903402c106c004003d030f440601040e03104030040036801004004010078140070071799072040d0f0007030900c4048134001d0b079110340b1900300a942030801224003280c8110480c1c0610420b101d400140790881c41c140a074500c104024810300300c3c040ca0803038440074151107240101308184410f00c001800326904185110015080303071140030011000884201142c0e00c080b0000342d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 332585206 1250 332583956 332583959
    0xe190c08100219030213210c120b0402090c0d0c091503061a0f040509040c0f0603020a05030c07030e2107050906060d15030605040809100e090601180e01030c 69
    0x244148407004807014036200450400807416600842e03c02a010104201036000401e0075820300d50b40300d071302c010b001d401942031406500f14101f2003c82c09041d00590341c401400c000001c008503c4082e945510750f100c0c4510055807655405c2c0803920b1000b605503402c64205000b400c40c15240c074402c41120040c82d0f581c0068003450718841002c0c45048810f94802c05080c91014041d081c2d12030000b214170b480342418656a8040410361212a0050b50020340d44040f0107014001801516485202070780c2c00b203d51043c207156141c0059040340300309010b440110302c1c140002081d40c900ca001806020703000341020039101d031011000900c090641202c20000e03810520070640740382c60400c0340d0b001410b41030314800064200741002507488c0c01040d0740e50400039206d407660450a66090503030001198000c00a110314146071070b0240c1c0075044200320360b00600b0040c1c2180d10b903910601e604800c1c40c10103000701206440d00401120000514000c0ca0700305250b0780c1002071a90710f400100f074000d5008509401e00117 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 332586456 1250 332585206 332585219
    0x140703060b180105060a0c080f0304032007030803060a0503100f0c090501021507050c06010f05011b0308060d0222050603060106020a0312021c060b03190216060e190c 73
    0x215804018240a240000c002c103040c404100406819101d089401c180c1301d410a141c02c4a0341034007a0b4009007032102c080350b0041001198001385015130b1107074517080080d03051440714050b410300852041c20942e0110104002042807203004542102d0007500c2110f115403a0030100b46002800000441c00301c2d940d2940d07410400041c0705600003c8028649840d000c1c1c5000c000035035501c1c0c041050b41070316100a004c00c130014028070480b62040400c0e0155140c1303603901c114200c0d0340407035441202d0110b04070140210036000d94403520803205ea4182c4a4034a1030321258103000340c1c6050080200e81182c040010411000b041403180604908207100c04102e500d041c1040c507080002c103a0103002075504c000b0f540d9001a0300708102c0d010404042c0c00050b254503981c0710071107e000e00031a040755440e14100c40441d03c0364000b402075119107100940080b1007a00e01c00070074201c1c840c02540081c0c10503550b0045000a070f064104005d028024000c4540e40c500e030184003504a082c981046071030050b03110081107031 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 332587706 1250 332586456 332586461
    0x1804051b03120406080903090a03081c0605060a03090c0306020d1a040c1e0c020901150206102601020405090916081603020f06070605011539020a0314070306 69
    0x4614207070007905030308903407040741c2c10140260b0081034280070f82480001c8624034200240c55039a98010200c604180e500e080c4400300d5445100c481e860110725a240085174074075405002c1c2104e0000d01a01d00c1c1c41d00e0808100c0061800d490122112801401c00101241c000d0001d419150b04102002480e4482c000c1c50086040020b90800d00560803c0003484502d43c00640032110701c18841d850781c0c4040e0003513504449007010848007c1d4000031900c000300300c031441000001c20301e210b26000c56080752100c4c0b5003160055140e100b15800d18041d0540e003d0054069403100c03819911a80c0050308158440000800d521405c540b05041c990104209000c804410301443c002001c40354050514100b1980c00c0b03000b013141c5400007030b006c0e40359101094960f0b20740070102d40740590400c01c100419619402ca40442d64400d400300e0b4000303020700e1020780458082042034130303108542c0802000414201e500780c2902c52080e41043e640055807a0000022071480780c03105c000000502c016046c2e250031403800c43c08 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 332588956 1250 332587706 332587753
    0x6010e0910090f08031b03160909140109111b0a0201020616120c0509040e0a1709090a0b010c020307060203040f12020f0d02150c1e010905150402180405 67
    0x990b00340340d49000401c1d41440b0a1404681052100e80d507603580c030030315265200c035200c1e5400071500000100200c0c400d46c03603000000c5450f00d6540104441c1e4443e2202e040c2d0b01c0c0400c1d100ca4480f0b4810040001d0340c202d500400b18581d100c80d02600741001106015502060540240c21a82004003c1801c5682c1448007940c000300c0d00b8064a800710f0082401001000716002064800c1d41d80c4c100103401601400a55801e0744005109001908080005a48414030010112100780700341048401d034100e418207540c2e040801502c140c81d595900c608180180045032080e50600c14500c1120016850a00c000c1018286940045039104c0c07030f2450b814400002540500300080d07209000e4401640d0382c844140c0c8044045800c107460741c401c0e000054000c0180a0029500c55000440039090840400c12140c4003c1140150810080112405007620100d19008000d9040202c1d03400b001c08402e1350480d00240041c10b168680c80c0d06406080780c0c1c02003075a0a903400c0d4050a92040107a40d80c850600 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 332590206 1250 332588956 332588983
    0x30c030d2d0504060e040605060d090210050f07020103200307080108060a06050105040e06040617010e0c03061006080403021203010f05040b0f0a0603240303091e03030801120203030c06010e09 84
    0x5031041d00320710081c01400f45025210070490303c3c00c00d0720308a58558000f030016140082500342d82c2d032660104080148607c0c0001c030b00a1010f010381620a41c054001d841c0080304000c54a4a05421507004400520700400c2c801003c1d4075003818001f010310410043c512032485900d6610036541403145413031a0041c0204004400c0d0b01741002071041384da1200030f0b202165025200103469403503140000d405415250010010448215041c07500420150840a0340140000c1036034114024401072640f6144120341c40094000485800c10101d4842c010042d402030081c81500d400501110f907851440d4000c0e4070504486424800900080c07810307104400f5050412140504404820000b141503203c0c00e100c1d4606041da41c4500744e10f1548404071514005803203003184000c1d240c40c0d20b80540804901d00960004c45a0341c0b00484200c000a1106002ea0350140c0b00c0d140b40341e1a012034411401180d0100b240c15010500c01c0a504007400c00000e80603008020414009240ca032aa0710315140e440404a13 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 332591456 1250 332590206 332590277
    0x1050402030c1011010e0c0a050a0321050409090c0501090e1b0901090f080114010b041404020922060305060a02040608160309051006030309050909061302030c030d 72
    0x440160340c0068024100700741a038400709044429070b419661040080c5208100d54281000b0740202c44007c50240e18140d000c59142000c01d4403002800610181808000c00c84182c400c0141003504016a003003500d000c051034054503240d2114101001c3e5400c0560403207500c0c4141030300344003641c1c002182e213001c0e080040024409140104400b440c4100c0c9194103c260300c000620303828943d201e40d0051002d4200c0102030104240d6a4107014024607a62034030380100300180d030006c43c074100204100d4041302d0703d00007954580c860b16020031000390301c00d101103644050141a900014101c101005020a001110001d0400c1c6075041040c00e0103001022030180a00c100301c1444003941144056400401980c060b03030000b90070410640c000d00020202410350720035500310143d03541d4a90000002c0ea48203650b03c8111a584406005c54030100355410000c030b40220000501882c101c01a00c84c0b2940018216200d0244d620042801c083c021003002c000265926548040c00b20000d0010700340131074004c41c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 332592706 1250 332591456 332591461
    0x90d082203091a0409050702030408070b2109030304030201240e2a0a180501080c160804060903060b06040e0112050f030a030b0414010f0b07050703140604020901080105 74
    0x30180c400308040a116003100d04181800d0925205203000b101814240018241e80c8000101c010450380103407080c0102681071500103003080d44017100b40c40845410000a0510600342140e84000303422010311101c0e0491849580c50041c081503da46010325103c10203980d403030a240c20028251404012080c0c2c40c01c504d4034466aa015003402c0d88e400700c0c1c554950310011070311800905154a0000d4402140d000318072540d5244100f41d00e802041e00001035160030708000f0716145c2c0300303d000343d944c0b00e0742e4081141e00c4002281e0f40392120040c50000c410a03034040c0c0709113aa030b5503800d480c2c00ca90007400001c2c40e658818000c12615110344880640115000c500302860070780100d00d4400140150401d0a40c84030202041000400c41c500600801a083c1ca0302c0300002c01004004094480d44248102d09101c0030710322440c6144500d606950a02d031400342528100803010701140d020320f1003100d02d031050301400400b041141028207180e10680018003681e0500740100300a641c01071704250403d0b4544400d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 332593956 1250 332592706 332592721
    0x4080d03090b0a0e03070b040318080c01080103171c0b2106010306020714060109090c050402030709090b03120c0a0c17070501030c050d0c080106080c120c090d0f0605090d08 76
    0x100c1d502c43d200100216001c0c4e0b103104103505500441ca0000c00449080040c482050f40081c101030950110902100102d6602c0000035620245c032041c442c0410031030b10052010170040041c42400d080171901e0a0320384041c1d0030031700c00b820210f04005008980d40f4100c081c8603142c02c40c0784103c108602301c4130480300c01176654581c0c2c032946c041c44010002640000c0c941c003000000d0004921131000641070b21103960307484003210007505a02c48110388154900e07102295900d400d200ba80e00860590382d4602e210340c14040301f14000c141c40c00050f0307414271420000d408800d800d60000c01c00041400041c0280c1501b500d4440d0181f0010703004a40090248201f00c41803410010f80306c0c00302c44e001d103008621200910b405807004c1c0320f281d4580c1040760411903d10758054100520504a03442c0d0ba0303035084141da42400c602514029aa11861101c0c241804102d0034000702001d0070380745400505e01895174a6a99501800480001041710305640354001c11009400034000c3e800e1014240c03e050b08507180c0100b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 332595206 1250 332593956 332593973
    0x908120a1d0309090a060b121005040c0203160201200f0706020f1015050a060f1202090319020402210a060b070221010b060307110f190f151104080d0309 67
    0xfa00180506884400100d135101075402540040100c00601030fa5480c4000c7c002c0501381c012070b261042d8403007c20b0002100e060500ca40c1c03074188655400755040003410103404403103032102c4006038108611076408012104482022a9a845004c002058a210440401400d1000941c866815904004000362200c00301054412504000d1000042c200c1484082454410f80503086103070001450ba00104d04982c0000c0c5061140c060341d16810b592415001c0590160300c503c094031901500300364070f0480760380f00003075400e290640700078005800e2030f1181107046d4502d503945901042c0c0080794001e1150301c0415125107009400920742162408103070780c000c00d005d9200702591442c4c5608c201c204001c10b030744c2035100b42d8804800904103035481c208190001c1ca1002c607200602118004c222003007090300c0c00000c50f03d443c0c2d5024400311800b1360700d0342c030f5442110300462400d6031000c0366040c90a80c003490a200d11380000c03040c122083e031981d0401031581c1c079200d01c202007002070500c1d100c900d80c0402d942c007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 332596456 1250 332595206 332595217
    0xc031206151b1f0504030e09042d05011a0112050709141908010b0a050619030b01020a0515100602010c02060a150f0b070501050c1206010302030601030908120a1d03 72
    0xa40703418800c69060b19840b450018003000905000250008a4603074401c40c1c1c102c01d01460181d681e034020220b5120030001c1405c03090381c1c0101141022401c0c5074208040d0340141c4035181d0344120800c07912490b5120182900c0c20042521040760000d000c4142640c1c01003001210411845401c220918209501801010719800740300a29403400c0c812170b502da65242030b40885a6000040c450440b596100e001d030180606070001842090f00300300105203428044150788102050980040c0d600d5480c4006400802d03624003091304500800104002280303081000c18000c01045815507070500d0100da1810408026800410071a4100141003030b02070760004039247c120940420001e60000020940c3d0180c1d481a0700c1410024049000040c0000c80c04002c3d15102d0300900003442595076040c0a25114070611002c01d0b10050200c6c085442540700354091588006e042c14001140303400381c0c4400715640c002e000454082e8084404201c0039020a010700000c1c01901d4000b02031030140c0744102c0d07440c1d020b003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 332597706 1250 332596456 332596477
    0x3130e04052104080d030b01090605130b0d0e06040c091b0206152106090c0f030d05070c0504050c0a0f030c020a03120b0d1a130f02060901030b03030c03120615 70
    0x228095502e58180100c11240109814001c03a00c2682e04400701071301621841001d907010403c43c010024181e8091800c5441d600303003034100380c048282400c04401803034001024481200e030340c03500c0702d900700e0408022450140f40289010140949000102c0303054600165807060900d421010080342940c0005880748c215446140300c0e4000721f9000f01007491300440404142d102d03a03107450080e080c0314000c81c03800c0c020101c0c0030903981c1c004c0001d024011240d1901c5401c90b0580e02c011a1255101d200b00040d201c140e105d403d0640c044c681e10400213064500c1a07401c0c410680001541c1d0f0300050300444081840c1c040c5007403d0100800403000a5100d581070100601484200468940b48280d2640081180000100f014000031880d06021110301c002ca100c00380e2508004000c580e9103600f441540c8003540d448100548400000c0e424845517411800020781450b8503030030040002d41e420310191001d448420001c1d41c45070b5030b0402400d200e130000351142c0d005800003805c900075814020200d40100d0f01 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 332598956 1250 332597706 332597743
    0x901050306130c090f0b07051507020a06020409141807120201090503010e1c051309090302010212070809010b151204030c080f030411011b110406030b0903130e0405 72
    0x49203004504000c2102d09a58242490541268001500129040d054031024500e000c007a64884009040034898543c000d00700f50b100d560584c18800b840d60705154805002c3c8182c030480d80c103654540301640c205810641c03401e0b03222407950711038080c000780c46640aa8504001403040210f081015101d481c6400340200316885038080c0d80559004e90b00440060801034002c100d9031469001e841c1c0c5814624460701078401c061059480c0075031042c4242c071210045601c00240d00c038540b007080802010700c00d80c00c0b403e65409110305140d100d140740001f481072210b521000703080c1c900820030b5801c40d240c0c10046480b4a410814088507548000245c400c80d18552003030440743d07242c608007941c82c01c0c2e40c0c0744018028040000e840504490b800c01030743c000d03803051611201c1001c0e240010b5550101e6030f044d80c02c3e035901410140d80411305010603103080c140e01410006d1300f561251100a410142191101d061754800603c582c0d1302202c80398920020210342401002a003005d5403000e032501d01601c00948180c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 332600206 1250 332598956 332598961
    0x6010305070309021203030103020111060f0c130312030b010201060503030c0a0b0915040f060510031104091707080702090604110f0d02120a09110a05060d0f061e0305070b04030809010503 82
    0xa0003548140b0f1101c0e0010041e02020300d10b17116080da43d600900080303000885415800c0103610001407440d00800c20101c20581958903455940c2490700701c0110007415118101c4004080b40c01042c1004100d0000d9030301203040c0c1d941c03000181c00d54115910041c06a1f2040103000740c005400309540c9a01940700030304c0e00c1142c80b10803200e490030f48942d1084072012000000e02041080038428441c0d01d030f1051000307114a5840299086030300c020340c07201900408110074070020518040d40801142c91103111000c896800d100201101500100812540b070000000c01c1c00542c40c0c98022164043d2040700c043c00342201c8420815104d0040115940505501050543e050b074074680541c1c0e144003101040280c0351401981c040d01500841c2c00c281c1d850070002540e4032203070610070302e802c0a803038001d0101490720710040c440c4401810140b0004c80500c4d0703500004030b820a0407244080c10028903410b84030714181181400b505007080b80c0d21a4801002c02c10041001070580003d403890441709082864495 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 332601456 1250 332600206 332600221
    0x1060f12200d0e0613120207080d170a06120f110319060515030d05180a030501051e04020319060f060b0301060e0411041a13060203090f0f010806010305 67
    0x4102101d22081451040191001c030440c4400282200024860051040c10f1200d1680d130f0322520f0550b1412910070841080c00e001c2017a42d0031800f640303009881110413490341d03000c282c3d0500711452400d0001036108420301c0507a9641d603140b05e03000b859400d01040a180f515940c070700706001303413130000340442c034040728150074000092031240c81c0c801e010f801c2d10071b00440c0d041d101800151440c011a020751038200441c41402d42105650312120000e8000c00c0345054032102a00d45400c81c0c0300b2030000328908181c03038406855120050004601c160300101c1c40e03040c580703410038551001c1c59840055010060030400542e800199004054080d440c0400c00c007a6982044000b0304020701030b03c080d803414850001034030894000118120307000c1e0b540b540381c4103032001700b000250740c0101c01405440d03100340010b000c1590703030b80c008041a88102c1e02651503d24183e0480300d03051080e0340410050b80001c9681d01990070044403600c02c592046540d40540a0301100290040c030340070380040e0415a5500c00034200e07 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 332602706 1250 332601456 332601461
    0x5130501121e050706080604141e09010e0f032805030103030503040303060b280203040605071209080607030203010306140c0d050c0c0102131503020906070b06011206031a0f01060f12 80
    0xb415000410360b00d520752645800341c08000143c525902540c03524150b40c803842c1c20070034907a01910012800e000410900500d41000d160040c01607a605e541e52007140356038503800c102c0080c6c5031074401c01464451006240030080c0420b0f0211a80d4140700c4513440021140d40041200d0640340d041c14441c0d00e1340c03540d0400b20000e000c60307004401a00c400081c0c1d190007070051011114400280d06105d0741181c03240f0703c01ca84034002c030312924001c25000d000c0035000800071040009400268a4020b48660b602e8000c18905441511000c2c0400d81c00001441405024020071088442c14000d0309003904100f2450310051194284403160143d450300400d000212460441d0a81c0526200954403503c0c08031b040b401144462049480d02c680d01d600c0352078110700900070380d0300c4118010105410300c130785911000c0b100040109840d040003c455985115126a407143c400614010f4030440503142c0c07451060000000050000d00180014800400420780d00c159203203459031107481c0480341c1d1400089a1000b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 332603956 1250 332602706 332602763
    0x105180a060f03050309150c0c04090510090305031801020a0f0c14030a05130905040f17040302150301030308062b02060f04081609020711091306050a060513050112 72
    0x8090107140000800d2080c0000039045680f004c58080ea11b01030b8494400d15203100b03230030070712085800a8020340040d1805a000e012034074050819250090032104140d421920365a10403804580e0201c04c0c001081145c140c4096507806550085240500000001c0c0070424003c000008000610700c1c00c0e010842d41c5081142c10746079500c1100d0b11055140e20150058100708441100c112072558005001603407405a14082c80e000070003121284100d0b201d4205402c0850b1512001c01001c110000c0181c0b83ca82d009119000138a0005032254110715006008080c0507101a100b00074101d440d40b95000301c0400e070541015254000308107014144082841d80c0100c65a4515220010800155a8001041c08040c0000d04c5240d000400c0d290340e602412400340c100041c1c40d4030840031002a41f42400c032011500f200100051004441295560409899048403900d04885d2914000c101504143c601c0580726003241d0f80c01d20103507052642e40c43c900758000324003030902000c402c00c03c00e000440400411 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 332605206 1250 332603956 332603969
    0x50f0a0323070501140604140f0402040e0f0d120e010207150b0109081606030c050316050a050f0d141008100f020909070807261503010b031006030213050105180a06 72
    0x5c0d50010380c414813110001c5035030501481c10820003c49211900b00b969205180904a10a13181c4864003840001c04e03090000c003501d441500d0300310043c03d4040181500d03948955803000c0a491403501c400c006d0321551040155580c1c0103216107000111302e07590030744520b18205000203510b003130717100101c80d1100c1c0f99010060a000d0301d00460403030b61850f0307602821342d942d40d00c09000c1c02802440032100d074841201d030341010380e5101521b108076a210348000c00b5660a0707450114182070821118202c0c07540000c0c00503403c159515510765103107104610044e80106407602d04c010716441c0488843d1902c007401c6049481968540c43d41100c4c1807580c0c152a1501c20180400c3e00078504264080c0030b10900380e0b4800d021603482114000242d040c01180068902c0b450b41c0c800300c6440b122004405140104030a90b03255480f030201070001d40b81082071400c040c144080c080303110351039030051119242d680808070310003d0501d1b00602a0340c035410500d110b981a000c16941941d900c0c114030100a10f01d981191 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 332606456 1250 332605206 332605211
    0x91e031b09040314040f03081201050904021305061f1206090c09030305030a1404260702010e090403092c010b12040f08040801020403030306051c03080c0a0309060c0c050f0a0323070501 81
    0x48223016030f841c00342c00e00c1d262115103548240d8a5004002c43c440040b10001c0d4000342080d180c40e0684210f40250341c000300003230701c001e02101d41030440c0c0c0e0900c840c00c01003c000465401105031b000e950b6005400040c843c1060801440c00b8940c8000c10f00c01c9107010240034010004003103900070042d540000518070300940f0742d28071400c1c145480d16440d071800d92890425007a00100c0703082c02c00c80100300d90243c2d42c141c580f49030b994540d105101c02c80348018000c6c4e042c050300200004202e4071000d203a1030f9055840c0e40c0b1141d1107400c0700c1c00d242d511006030055401c01d07005000c0150000d008104a5800a41058202c0c1140341e1514180754184680d4002c40c00039400031a00104264142e040201510b0007140c00e0512150300751194003010b60044800750001e2100004901d024406000410040301c035441c1c0440c0e881c0d82a103a03801510003500036080014007080e00c4105203d802d201f041351000381d04001d03005241c0305440003010310300c0751031200303002921002404000e01e5801044406a0381d10100030f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 332607706 1250 332606456 332606459
    0x6240a03080a090f0f03060e1e0309040e0f100b03030c0304090501062607030b0102100e1c050304030503010e070509030a051e030906070b0c091e031b09040314040f 72
    0x10391500040c0c0160082260340e0f0b00801d5480c040340f00c180540740e240840f00c0a852030f41d101d001c05443c0c081025800c900849080000c06c050702e402c01505803662034011550741c4146020b10048494103491214113411174408414a01c40120300c510703200c80e1090b000708090f003000c130000b4158440c1070900c170385520001500040100e40b54000301d04030345e141e4891500a4201070340703001e02c1005c02e04680144601c543d000800440c00399200ca141c412041c03040300c42c140402144075040366648040c0400e258056841019201742012241d048100303c1d2910f2401c42c20250380c0500b890006000341e2050700340d0000000d42c180d00c60030540d140d01c4401000c44c0c251415a080c100e495130200401080404680e0605131081c150020440711512400760080b498444030b5280c084402c0c80181c031180517170340108490340d01c55071030b880c004030712008405c4104003c41840b000c00d0b2070803824003010f0400f450148801040c1743d6521a403142e005c4c0e01130401026440c1c103203e4180d400c1c491070b001000304030582c550 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 332608956 1250 332607706 332607713
    0x206220b0307021b0607030e090403050d020f0d0515010507030e03030d05011d060103020a17060f040504052401030c030b0709090e010b03070902190507060e190308130506240a03 78
    0x2a8131008999180000010010b07a03418003900f4414214082c02040c02103d0313203034490504400d226030143c0203192140c24900d001100701c0c240c0e0701031074103010340c0900800c80e461420303214440c0c240c000c03688a0780224101c8400001800384d010b0103101505000d6200d0a5415a0710140101c0e00030341c0f42038000b0051582c540c902081c40340c4001740d508a10300d401c03900081195010384221104034040342c035220071904010007030a1300100014155034012084680001c85d0b40c4642c010b09004a20600140c89840b0240102e00440740c1011052404842407000420100c0d552240c140306890b04400c4c2100c4560301c110f015a00e10200e0b601a002c0716241075600360b0707c4401135010306007092084050b982e103259203042810030b07409440c903071841c0c0042500c0010030042c0500001c0203000d00c80c4101081501e0041001800c1c505c43d80c100742c60121903108103404041d40110126481921400d440769980415100c1c0c030b41e0343c08010f01c04031340c012160000b00e0070341484500611550200415202c4441c0c0c5a20717 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 332610206 1250 332608956 332608963
    0x3040f0b04030f0e10051b0a060c02060609070306030b0c0705010219020714010804051b2202030106030e0610030b151c0201080106080106022a09131704030206220b030702 75
    0x1099500020741e145850a0b071483d150440c00c02c07024880e41c400703040c1207e000c007402592100300410340061003148100d100080d103a00840d4078405064001c0c101c185000740500240650003840c1780e0425107803000074400a4080390b40c5036040813451050644a07000e62410b6070080c400c003000c2d950906208100c2014440d40083c903c42a941c98001c20290343c101c0c8801521070311070a4400031b0180e0444c004031a039599080d021120712a00c005c01c40520007800340320106000d105554140480c0307070008010700c00035426000361911310a11000a003040d280c128040c00c1500c405000007484a5070900200d1075a203a0111102500c1000526210401c1d90300d008820741d0b616141c0040f40400c070705400020b035080c05050032504840c0b190b0050b00060b445920051098410246d040102c0402640e4039965511a480005c2c0f1449910070030381c0c00f0105a0130020364400c1c03c03480480305141c0400041c00161104810369004c070340c041d040e120020012603441400204d032500090203002010007003015095000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 332611456 1250 332610206 332610227
    0x40c05060d0c091202060d09051203010f080d0c0f020d0c1e080c01020f060411210a05070b03070509040b0a030819080a1b050711090106020106090b0306010e0c03040f0b0403 76
    0x143c58201072036076545650f140780d03220071a001e0740c01102803003040b40e0055160002540713144200e050390410303078140407081641c1d0800e030484103002c0b0303d80c00c05100c8000200b00910464010342025030014540e0390b960035046c045580001e00581c0c1e0b80d50031000700942003207100040c205841000c0c0c103a80200b11051002c4609110f14480c0b4400d003041d40c0072550002c100d00c0000100d600107012180c0d11038640c0050840710700c401c0f80d0043e040700c1141d0840162030380c0e0320800390325181c003400d25000f060610502e09019070f0045c00c0c40340c1c1700b0801c0c0302e000c6402c03a003117560800080e100490f909804000164003110241e0000c0c1141100284d044603216509459039194155611051400d1319a030100b002203c082218182c0a03552146441a2480c01003000d4804244070b40c00f034100c0c2060210101c2c510a8003a4001005031f91194014000c9115034020884500c00507001400190300d0481101c040050140c000d800c500e600001141c00d000400900030840703508403038554010305091038000c1c441c2d02c04 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 332612706 1250 332611456 332611481
    0x3f010e0f01061d0c0f0903070e2a09040c02150c1b01090c06030902030c03010c08010f06110c45070305090606040c020f070801090311070605070308040c05060d 70
    0x70080e000c5604005600040310711074442c40740b410140d80741054030b00c142d4030100144070007100a104410440d0313410010000984040700e0b0855140c01d1084041200c541c0069041c0301c2d03444ac1c80324141854401800b6902104000c586c0400c072603500100aa0510810009500c80c04101348100302002040100511840a8032102407680200021409007216481038000741015080002000040e00c0703900889941c3c0d0004050340d2684204c04c0010342111085001100030a00d0b0400400c018000c007074984009007803604115101d601c01506090701c03002258000c51240c05181084001c0322003501084420a90645c600c9043c81e06001c82c001950303d402003c0640c800d18440001c408511038000c4900941c005001013540751030340010400540031070020581140b0405c004044044001c221b40e500418040e0300003c1c7c03070a4141001054001a4008020701d40d100c035808001e43c171b901c141214042c54152420a069481d42e281c810413034212a4003656004001094140041046900c8031500300d07a07 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 332613956 1250 332612706 332612711
    0x1204111c0b01060806100909050a06090219030516210e070603020c100e0607080c09100315091b03020a20010e07080c0f0609040608060c0a02010501053f010e0f01 71
    0x300d0100b0000008446c3e80c1a100052000d00100640e5100d904545d0b0442882070340410b0054480c00c1640480e00462414401c000f00d2013015403540b501403085540044401100080c900fa800b0406000b0304908804945084509143c0200c0402142d200c1419010b45a05850000b951220000e01a400c5040488514014008008171740c0f03540d44039100209120750003400103640e50303000c240c2c2c002c2002400c02e068104108405070035552107070203580c9400c171070342c800242c0075195140f15002242030703410510405240c00c903543c400d0404244000e44004880c039015079034040c5100116924209000040c4552403151281c201402c01904440301284c03103d000c81e4402503480031425581c03c0000ca00b5500101010239903041c2c1e00b82180101111600900041581503407100a580b0f01081140c984003400c80206800c25050303828011540184800c0382d24007004c00040180041c1074285008140c0906a82e44c2e0588101301c10390380825400700c45000030032200007060a242c6d02c0301804c48142e0050351 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 332615206 1250 332613956 332613961
    0x2100216060f1202032502010f050105040905060c031005030613050f0c0f133e04050f0609010e0a170f1603030302030601050f07050706090b1204111c0b010608 70
    0x9104160420300c1d1056641c03151001841c0c0e1000f1070080d84003602040c04006203131001ca0400d08400c80452400000b82d00000f03e0064410b0030301f0072500103801c030038030441c00c20342404c0c00301340c00007140354001d050383c81301540e2030316580b03010080c9200ea94000c0f84c140c0500c2c800c200b80c804c07601d0710049840340070740e06540f41c0c04034102072030fa16035600040d034560121142030522918242080c1c5943c524034030040000d6103002e2110340c028098074010310f0046454145401501802018403d00030301110310007618206400c050025a0703002c03a6601c1d05000da10080350703c4034141e00c5160740f4040301d207024120100c003948444c00d0ba05003841ca41d140102d948942c01d414001030344e0008004d001103c407261602113050031030b80e00710041c1d070010b0034003810410203015079031100b0844401880d0b160710500023005042c0c9842e0000e8040034465201d8104108184039480600100d50b08940d8095840b5589041d13603400c013400141004040d4003907800e11240214403d007080740c51406241601e4090b219031003030f076 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 332616456 1250 332615206 332615219
    0x10f0c030e0c0102071406071e060b01020a120309111f0e0a060824030f030a090b0a080610020f010e1b030a05070306050c04030f030c0b07050906040e1302100216 71
    0x9800202c4180c3c01607000201c1001002242c10003250340900c000e180615003603451300c420408824042445070758044407920703002000b2440c030a41e08000020f001400f090a01600c9112103c001c2c101080103054480054070300300100703007000e4094500000c0c0003c0002010400008030307911404c06240105081d2010151580340008101e03084800f290b40c0c0005655441008a02d8080c81c11a0804900000610034400c2e607801d21803d1510642d240c0155190100098001c1528042e50701c180e5203600204040b001460303000030a568843c10549080100e8540040704920700301c00d4920007010740d443d140b0909030095000c0355045040107082c03446408940388404050701c441080000610303e5001e1141000007500580069030700c440078a24042c24603540352150420b003568404103c1c00121803805800c104003410214580168441c41d00604181246001c14084d20940c041c6054101c44040003a0b00d07842c487e6aa010420780c05000b09040d4444014087d40d0303034001c1380708992034241181011824 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 332617706 1250 332616456 332616463
    0xa02120304120204090c030f0b160e010801090207020d0206030c0403021207060522030f0602120f0705040506131706010e15011205041b1401110318091305010f0c030e 73
    0x65441c000002c95641045501304401004400740c1160000b500322400008507400039403010905025202c404038034603100c819440898108030388001070100000c0e100d941c0d070744c0c00140079055829015006036203030300c280005008410052002503016800108100c1996880d8000c5c00032a44240c45c90f82c5a081c00102c800d44a01140c0102000501c05010900001884e42482205048221104001e158481e02d130619060a981c2d0107652094000039005000241600f440d54001c507a0821504075051811000301a845144103051156402180c082400c00c44040120001c200d08500501100301040c05691140d00921480c207400c0c1c5080000f030400c07003401002680f070040c141c2d40c6d4200d220504050708000c000242c0140c4051980c028460b00004a01c5500c401400a01921090466800c0001402998005610714051f0010700480d081c41d03054140070344400c00c0480341d0360508e80d02c0040c900c0148180c040050040e6007440c400114194030b507884100c1070381050740c0c00e004400795440e00d29079 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 332618956 1250 332617706 332617709
    0x150606021002030c0a08041a010824270c0d12031b0e0603130b07030504120513090b040e031602100503011d060103110d052a0f0c0109080406020a02120304 68
    0x1a5020104800c40c5018891004154071a200c2d01e0505070300e04020040d42383c3c0000c26000001d603a8425088048611415001c42d41da0041c0e1843c0c1e44040e142c104d000c0c1c8121104120790154072602203805090b155018042c01c01c00d098003800031088543c850405541d29580405c00d01c1c0447d10307251704003030200c03e00c0801241c03601c0c00f510b802c0c0c45144090144019a4070051200c120310044840a000143e0700c2d01c015401000550740110701c80c14a0300f44210f401000e016080284481001390603081c100e01035420080f5400060002054090074000c900034000c41d0020000ca4080020215040f000000c085802980240c82d510107000501201352001e22082c02801e00101c035100c40710608480c202101503110304113140110b004003100100202c540c0003001c12107106615942003000c40382140750b02520141c2c00d031010f120010143d8007515410710907d0072202100c02c0001d48680303044400d4001042032030744a0116540d460380c921000351282d040d03000807882103800104111091800006560 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 332620206 1250 332618956 332618971
    0x9013911040e03090603010b0901031104061e0503060d0209060d0516090e030301034b0b060306070813141605010305060a0f090f09060606020d08070201061409090a15060602100203 79
    0x1b0300d103900701030b60103a00b9003002c1d0210b41059110780c05c02e1040040304020b0001808562180e244040303085000030030024000b0168030070443d043c42003040c1d940d0f4080702a00e20b250143d581da41d0303030303211300c00810844024024051b1030b82c81410348290824000207004011554500780c2080001c80e02909039880344028840600840d00004c41c8081c280201d07054084c034001c03203010744d4002c80c0321560007813402111007603210032003e00c0c034468905010f006500325503c4181103014120301d140c100c0c2d006c1e00030840501201c041004032400c00c401c00c051550f0002491091408460b460701c481043c41040b110603000e1180040d0520010900300d080c40081c10041d94418001c186145013030084507002044554880d000701901d901c003c401003902841242d015200382e5000c6c00d110080010068461038000c0c0020045a2404a003008046080f14064006400c2112604041e0311b49aa2040c0341a03d5000701078000d4005200c800d01a401c554803131011140c00d5000d5445101c000c002c088102c0c0403c0709c012 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 332621456 1250 332620206 332620219
    0x1203080606031f06090603140c03010312020304090504050703020103110306030d0525060605030d0c0b0f190c03060303021006030b0109150e0114041109013911040e0309 74
    0xc5541c034081002d50752150200c1c5022040000c0f88074030f00c0ca40c085580c40364020030f40c41a4103002203a0f046c021070002d80086c440b07017000c0e03052045040c4104c3c4030500c0041d01a10507403460b0001c0034401e004440081100d070702c0c14030680c1864100f4a07201c5605200c00c0b408a454040b01002203103900c810740e88200b0008000e0043d0f405803880544090340055620504044160030f00014074503031044846809000c1c0b00300040160800080c0351408407100d450a040c8000c0080e8000004c9041d0304255025407030a1100441d07480300030121010216903010414080d04144d030304034040ba41940201d00f100d003c0d5086490f00090005100111051404080c11351b40e072074001404400031075040640010b00c044002c100b826078032100c0105051080e00594803001101c2e5080d42c2c01e1400c0c0c040c8100c65076013042183d24200850b030001e4809000d0010340c2040c0041c004004042400d070103034003082040440704030360301d03000c5928019410340c04400c000d81c0f10303d1900001d080140000415100c0a600143c42c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 332622706 1250 332621456 332621461
    0xf0a0b0102030d0c0912030305010e06030703080a051303082101050f030a1b0e010e0a0c0203091e010c05060c0703022503020d0c08010c08160e010905040b0418080c07120308 76
    0x164000b03013502494403014810881d4000507038420700c01c007072011640070703607800500d82d41044901c0b07001c030201070304107842540080b4062010601301021107112039101e00b0025039880c00070000b4242c40300d0b61ba1000d040d000300821b032085008820b0041308444484031080c13816507a01d903010442d1451540c0c0360250186e201c0110034002540469520a4015155419801c001d59070755244402501c240c110041147d01d4005100c5a1500c6001380350b0742108600140d414810000040755003c1101d5441c10500801c05039280e00390b0340211030000c80c3c181c216040d00d5151500a40301c1006901900c002c800502c60002c1e55450341e05418013059103243c104203580b0b844e0f4915020000d07448550b00090311007081200b40000c002d0300901c00c1c00c481c1e01d400c1e1034882c514a000d4000b031000403400345104044c40b5010b0396480d2140c2c4d00c903644ea81900d600311000240c02c3e4150740071400400e10809112468480e136003031102031041c104040c202c0700100d4030458201e2529941384a40701051f615008000c148040701 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 332623956 1250 332622706 332622727
    0x3050607090e0c070501020f0d0204050109061103070308060d0215300615120405060103110303070506060405100b0f091c08090f012703120201060f050f0301090b0705030f0a0b010203 80
    0xf044c13424090b10000d414030003485640003041e40040010f09089900241c10400d5507004400c1c01c0060140e42040c42030446803c54031510391192100c014100051040010b0507035540350814a2000c0e0094140840d005480141c1696980452103404a420340d8002e10b68100032200003045151982c04116211134503240244003061860f032219000030b80c010702201c0c070111309058580744900c0c0120000c01042d4510f0410f620b07080480d480d09030094004200c4900802d10002d01290000002e95000070588e41d00e03c10016101c20030780021181c1c40001640c011050155806403070b59840441d203040c215012105484510700c03070407000401801082c003030140980380101010f0f0088074181040c003000140051032407000c103003510080c3e141500d03c03281841480800007681030f040920380000c2001c54100284d417000d0544d5440f0b038600c20040391002803003649081d0003070490380340e20500c0d8520506144002805c1504111713a04e10f20502000001152401c2d2801101901d0700181c0103103207014400070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 332625206 1250 332623956 332623981
    0x303070f110607170904051509040f031803031101050901090506010b18100302191107030209061302120108160e0c03180d0c020a080109110607030207050402040f03050607090e 77
    0x20446039024605008420100d0313801040c1101c01c01c5181c0e01107503103143d00002c10044502c09000050f4000b41030000c1c800e1500c502648a030496000510b808000c070349894115050b0803440301403281900984000401c0542001c6076100ca4000e0348020300141e41e410540e507080303540c2c0704000340003540480010042c1c95242d000400304500c0b005110443c40d0103410100e0312020354515590000396002440d8002506178000303200c1090130307601d403a0400c0c817000c441c40383e9a041a0b000181c0306041c1c44000c00c580b9030396100048100281e0407030a5496400a44181d00c10510900c115107007030250002d1208213000d42049501505c0003154100100d480781850a05076401c000d20586142543d8018892806003c2150314410202541c0300340360300b0340e40c3c818404214082d07030028135103a041240ea80c0000318800d107071210b11101982c0640d201c03049410120b20f0310003644d000035000307840002d0100e60340f155482024260b038060005c49a01d40c0b510242101c0c400c4852080080320700b10302c00415514420b64 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 332626456 1250 332625206 332625233
    0x3080403110321071704050607141b0105010501090608010b0d022115012007060c050703120e121902150c0102040902090f0a08120901030e0a0609110303070f 69
    0x810441c0d0801103c1c003110b40b03040c02450302c1c4008411420702080407069000c0a1180c00319050102604141815030359140d41d00c401070401420300c80240b20100c9203815010030744442144049600e07015207540c0002070b009040c00c0c09a140082c1002c6d902150183c01000c645048501401da6203142c4598208204004e401209a0031800c01080d100c4800c040341b16400280104482000301101c0b1030400d0001d40110580e94200205401040403000c2c00a8081001012920142410070706400d42d85402401d20800d42c0005042104904003210810761203403070381c80b03180f0702074811120b6000400c40c000d81d10749951a220f1910308030b5101c540d00500301000102a07440c400c206041c240348001c03076100d003603800c46c0d041215460b0380401d01030f00d503150213511155601d4080e00d0b00b1485504010740d17146c030781c0441301486c030000100148045050b40310b548000c1130401440c05407070442420386000720140a01050036940500c48402001851030003204031201c40b54445043d0540c00c0d40c0355194551082e04 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 332627706 1250 332626456 332626487
    0x6070c06110909091501120c03020d0f05060c0d05070e0d2a0608040c060306080a0605060a0b180109050a2904090905070e0106020303060f1c061a090c030403080403 72
    0x51104041c19111595182e0094248901611210641c00e21108901034140d104c43c61008404501e0800300c0c40c0d00c1230150a41e41c0555261981a159051400400455020080c1984160020003801006d41d402814580c1038400b001d00a0761903040080707500c14034614800307911100d0a1203480018400700c3c07069a07007092440c00000c400c10f08440b181c0b0790308078070390004020403040d80820041081344000803010701818201001128180082a40e0320740f82280020216961507010840d1581e96150003401400ca0341550b543c5d50304036500005226980340105c6011642039203020034130349000950302d01503901907101240082d01011100400303041940405c0f441e41c10810010807004054090406558080c20051108610f40380400408480503840001190402d20074042660707101c222902c80076208a40300c025504042e801a420b910480a00400d003502c1e05034001c200540010056461420031243d4082d5669840307000017892004540060000311000300050020b1b00803031068000860 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 332628956 1250 332627706 332627741
    0x16050c150f091207090b151801140c010f020a03184103042c011a0c070303031e020306100c0c0f0b12090309010207031104110f120105010206070c06 65
    0x84800c0d1180c1860a103400c85030801b51103614850682c01c1411010522031805110036240400d00009034041000000d07401d4104104000d801030740c41111410ba500480323081c8000c018000e90410101d000354483e00c4190082820010030482498848048421b0346401c040ca00300081d24440f20044440c1a998844840314549500101003135034120280381d1228a44c80103681d22424000384c105050045841c259126100720940340c3c0e08a052030880d811510100080b12126026140841c503500666a0102c41803280101c000300349907068122118001c102c0044903024811381c14504183d05c800c85001e034000e5102a404240c0e81d108035804648540501d01c004100c607224458100b200c0c0455014101c0140c0c007042c501806144190001d41091003840103500d00040500041d40b01c0c0d00d2440098a0003d140c0d0420341c0769107071078100080010070003403400c1d0b42d42110700140307aa0703400070184181c07111541000400e42e940006501401200035855114000303800340d4440703000d0711200c8c0c8940c4d62a00c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 332630206 1250 332628956 332628979
    0x80c0d020d05040c05010e240a030f021c180519020303120916270906060f0602011401050102210a0e060a03050402030d0203030712050c0f16050c150f09 67
    0x15070b44100e5002c3ca200d060045002407400000400c004801020948120440351107915148444c64603010101041c0b0115529811014420303002410001c0001d02c0e00d0340000b4111440500c648041000c6034082e800800c07034466010034500d40c24018100081c419403103000721211581d658042084c0c428801403c1b01c2c9000300085000c0b820702c8081d6a5485181d20090390300c0303104902c60302c5c080c0140c070702c1c1c2001c4400384d000c00c2c2e940d05001504400901084d0b0340c1d91621411b010090300143c014180807042d60010680d03d03c1c1c000c5c028180105003d04844068001040e590f201003003076440322a034441142c2075808540d89000b0160f000e1380d041d030207100c0080c1640d1400d48600d0041e1800944a440c00103007850107005141c18035070840c07840c01c1150030410810400c0c41d00708504a045d40303a034850010380c41e51a04076011042c070420388204240304e401320300e5a00d070100e40d81c441c2d04464460340644480f40c1240062064186c0914682400d035082844040001c04c1d2082c040c1c5040340d401042d245d00c20 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 332631456 1250 332630206 332630227
    0x15090f0706050403140111030a021305040e0309031e0d121e0b090a091e0203010e071712130306180b04050f0c150a0c050a2a1401080c0d02 61
    0x19540d0701600100d58040340403c2400031034005106082c060034024044040103080e403201034070000309080c03616580821201244202d44000c540600303805041004a80301c0005030603641c0c3c01c1852030030700c03034441e0034038484003841c0c0c40407043c00b10b204440081894440d56031095070300c682c1040349400344d240d0341d541580c9240200c10b0401603900c011440007480614010602001100040401da44141003402c4840040c2202101401c0c0301c850290b18000c100003480041d01611207100301045502c6900008940610441b0690068040c50021107034822808540c070100c60048038404020303501400410004030300c1c19000000103984d11500000754207076554420007001d005480c1526980c2c03000f410b02641e070104218049072f1081c21109036a44101035a17010b010341c0700c0c410b0864100920854481c0800c1000c11a05100c140c1c000b9211516041030301c240d4510351803881da16100c3d103000e0500050004440d44010180e500103035515011070360798500c071240b80cbe4002078801d1422a401c00580100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 332632706 1250 332631456 332631463
    0x60310021e2d0304120e0a0501030f0e10050916060207060309081c0f060f0e04060c0e10030504051905031b100c0504090b06041206110d020d051f0815090f 68
    0x1000042e00040d89a052034145030f10162419208001403010459195890340d032945501c40441d94240380104500b0a4200d90401800c028400090301e031003001201c0070090311fa40c02091040c0d0401088540c0c0010100d0038601590322885543d02582282c0c0b8103100c80e912030781156024030b00038818070f4a0600502c103001c494bc40d01d4503c0c83c00065542000f095801c24034020b04001344001c0c0c58a00390103050036150042c00d0400340000704182e503595580c40b1700c2c40c029025107042000041c036124003142d0310705020340580011142195140540c2207021407010789540b0460449403c1002941000495540d4081035100b800aa0030705200b09001d10440e042c15014804004003181d88040d121450400341d502901c10092002d485190180700500501114a2007407a1582e0804008140355407040305d580c186209640314405207a00000d4124214061900114050000c81a4110306108500b015075890112402213980d10380040c092000c01031001d01d07000d5000182c031800d48c4d840d5007104044624 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 332633956 1250 332632706 332632777
    0x140903030601021006050f04020c251a0a050304060b030a021003021b0c0f0907032307081308031515040603061e0503030415180806060310021e 63
    0x10564000001c01449582c14081d0351000b04485805015090a2400040705c41510400640c0a01d50214203070924190800c114080d8900b4001c04001c517003c080741000f41c03030305c590044103d50008400340d114002060000c6451000d43c0d40d03607540c25500da6076101c0d00a01100384c405035041c40780310750398000760745c134220b10240c01041524010baa8003038088141c41c9145a042c0c648240b608000342030001a21220383c07c012202040703405a94940d64200140d00805031001d581130041510843c29500c40e8001948a01654007074903600c20030b907110314a080f002c0408120080c4a0303101803000c280d4801039000c030749841c224010200d41000481610425454019500c07240c0041c0c5c90700c0341003150608022130010703414401022b86500500b0400070036500e20903841900c401c1f00f071000c18140303854412a24410340140035524890400e80d550261903407114195000781c403078020204903c814007198401c07641e4907450724104280701500403620361505c0e0407041e4a0028122140301c83d900389a0b401d80c0744207 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 332635206 1250 332633956 332633971
    0x313020409150e0c0102150627070507030e09100312030f2301061b1112030a030516090e0c030411060a0224070e0904060f020f0306040b060f160614 65
    0xa000e00441c44070f51501e126180f200d4195000386030340400d0104d02c10560b03503000360260390301c180075140e22801882d400f42c3c1c03800300c41c001c50020046c09141680140208049800303562440580c0c202c810170409030380c2e82604c0c207410100c170040080002a00d143c2d60a600b0400c0e0741800541c40101e00f040606680c1054804411910260b6140360b03a8144214031501410311480d200500c00040364116000088a485c00341c14005c1d60303088116190b96009200120420000a403903e45100081c003401915003a1a0250f16420502e07081e680e09100c0e00800088507451070700441c1ca911580b0500b051580301800035100c2e4801005035407015100c0c03400500d07050145600074006c410580c849100c01d9054400d54146003216001444005544001042039402088442803400e444a01c4c0c2200141041071102084500100b04a05002c0401c0091441190700781c4081c45400400402c100c80b40c8a4540e0742000c3e400c050200c00d0703156504180703400700039110b0702001548806190000c04108030484604 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 332636456 1250 332635206 332635211
    0x11010e0607060b030f0321090a021008040b060303180d05070b040b0a09050d150b031c0201020901090527041e0b01030201120608070506070c0e0f0717010b031302040915 74
    0xc2c43d2401c04001c4440401100b802a50400b1000d989007854001c1c4540f1480c00f0000c0040840c0b00c0820520022142c540c0c010a1401c000c201514003801c00c400c12202591149024400194181404800c542d40030140b9617a05c206206501d040190f840b107012016540741c0f280000104a503d40d42d00200050040590ba00d5120f003954080180780c01803a400c4940034412030090f11001582c584822424028031140200d8903c00f0103012070318107440a42c0e000c60703076181060a40e021580650080c01320400a0340d4191080b6118800e000c070416525404004030307000325040460040b21950255000f80c815000210700190224a540e0112108c140a448001e00c2c04010070441d0b800c04215014004910002e1020501e400c0e102606d415603407245902440c2e0008203201000f55601282000e455002e01074a801d081061142c460140126902d401049080001c4404441e283c900f40e412078542d94200351031036030790080f00c0c0b02e003c0081c0c1d03040b40c103c0c0d15806540009507000031603000340c0c401c0303a100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 332637706 1250 332636456 332636471
    0x6060d11280215010b0a0507021009080d09080d18031a070801050405061f050705010f0c020c090c0d09060e060708150f030a0b1003050607050703020d050406020a11010e060706 77
    0x44204110710103814000355401148144040100b19400d01e04460342802d40540ba9111400b0035141e61180d044020741c0401c0460b00b0304002500490400c1c10f0715000d0f0100c4816800241f4184d8981e0128042c40c16580c2c400f8944441c640d1190b141a44040c1850b50a0840d85a80341d49101c1c1d210002c119822a07030303420408004c41241d100d4070344d03801400d08580500040c2040000b14080039400c0c5180c0b1042d495031b10440341424010720485444580c080001c2210704c02c10160100240342c48880d50700103004401c814502890a8000780c0e00070b00700c2c044402c1c0b4101d601c100460051090950440e030540d29021140c1450303d05004480c42040745071112000e034a011100101d544845800003403054000e0300d03062070f070782d1400036103a04026407181c080c0c0080e0b01e6807070301d2500c003013044d0744014118883c00c402c0010813680000541205031080e000c440d1422107101d820380d481e001d00c2c018140103a020101c0b40d4040f40002010f01c85410041c14403d40c030941c81404030b01c459108404c00d64109449541c03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 332638956 1250 332637706 332637757
    0x1009050a02090420010305011d06061303081201060c1203050910020a02010e2b0c0c0305010c020a060522030509041410060908120a110708011404110a030b06060d11 72
    0x4141301504404d10b000c0242d503040207100d40080b4404001700c0702c1034101c8000220241c88003412910010204411080043c2c0e036440c01460940c085491072602200784400040da02d406203130724480480d44646941280c0c1d00805c8102d0041c00000c00c440c1246c4104140343c500a09148010004600580e001003404042880982d18201c220300110b0b44044130008084008080301030a410002c0580ca0b00181c84650740c104101e45803020b800c064225407900c41c0842d201600007484c6086240311700350510071a902d4404a0782c0b5400030095881145811a000e000024407400007402c0481e80104000789081c4086104452108111303000705420442540030320010343c11482b104010305480008050025402c2482601c41c060320324510140542c1e40b60010b02c00000b442124054042038000300b1060104844030080540182c800781d552802c901d00246203030902102200175070350409482419a1541d00a0284a6208400766900540e4070507a021010350354030b00030310301100d10b051491a10000c894 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 332640206 1250 332638956 332639003
    0x12130201081b041511031912020313060f0f320108030a030c111204090e1504080d02070215030717010e1611010f0f0b040603051009050a020904 63
    0x42a0456521030400d40784008100c400460b02602c9902500040110004c2415166a40180349071015404003091a0580d040411340b088042c01c01369946121208a180c0c1c42003c91005440010740710780310744d0003000851b62582042984143c44800000e81980c40140501159400c10a19503202100744840c003800420100340c407555048494818019403510414690740d04c6020a031100341758032400012240741c024003440c000c0704600000d5a25510502c0010725041d44a4000c290320640342c8003000d41c0d689e900040341e4881d0860544c0c0481e89855548481c1040d030005a44548440c1e0204074240040c4c0318024401d91643c40e5100c0c10f501c030b0070704c0e1102401006c00180c80701c02115031840100711200300034165a4004a880c60b610400da0783d94107044a40040307001500c0019270902d00c040c400700030598081c0724880603500c0d0810241007510108020340385244030260040d8081240d1303440e100c05660105010602c180111600706400b0303400314026503421641a5060051880c0001e000072414 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 332641456 1250 332640206 332640211
    0x2040f0b040f020a021b011110020a0216080d2003070c0321020a030c080d0203010b031806061e040605090108060f07020606060d05181f0b04110f030a021213020108 72
    0x402c0d065052800c0324a000799280178103021107213001d5520000360403d034003800300079020221200980e04000000040c0c01c0c040d502011a91005128004a1141d64403504003440d0a451900c009065610b2082c46d04035030b162004039601ca04548110000b0780022810401040524030030340c000783c2d03901e00c2c1d4204a0340b010104047e1a400c0c08020759601100c0340e0118842c030a107940340c02d20302030614650078098418001c02d529003d10b1840007001140c60202000510300c140c0341006190310722480a5201500e42606070343d00b42e001240d00b007184040c6001d0700240704050b50060000a00d0340e80da0380015540180030303449402142c201000b0700101c410840a495444903190000308158101880800c581d0f03c200f02110b50503941c1c500c0844c41d90166209242e88a058607800c5840000c240291070b8040c0d181c82c0c2d00398100d10303c1c1c480784000034105405038000ca00c0742c4c40d00031400d200701c4014a08103980002c01c90032a041e800c001da080e40c00c440b03182803401428000001e400345942440090040c8501 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 332642706 1250 332641456 332641481
    0x10b1e032a060c0c210c040603080406141e03010609170601030821070801052403071112070807021302120601050d060305070b1e0c03071e02040f0b04 66
    0x2080c01e484100c2020214a141d09001500d810b40e40782c2d0f6001d203150914421301c0106a00600052000000c24480c1c110074805400d644280c82183c0c24600420085800a00c40244060f2050100304445070082402c5061100902c14207890f010ba00d0940172040fa4102919103100300c80840107100056011800384098130100036140107420346810000d80c0c91005100040c4207840015008030407491848801d4954509442c80c5070041c11f110340c025090ba138003400f8880c014403040c5041903101c410101d54800a10140d103d0505d1600ca5250886070b8911503441c00d8610b04c5a100510311400c403e40c000d0403090300900c007064440708144100410078200340c4c048a5014014171503042c200c8041080641c2200c0c09080071580e8900c440304c0c800103031415600c042d1003030203441400501900448020603501e000b40c1c1080e007070800c1002c420300f15405450700440c1503510500011000a20100800c0e00e00342d00618100748507800c550004040d12901d071210300c5041e80b40c070183e0380380b82442d00a0002c00c590 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 332643956 1250 332642706 332642743
    0xf0503031201030b10052e020d09030b0405150702010b01121407081513150806040f0305030c091c0203010b0307230f120d021603030f050c010b1e03 65
    0x84141c0d844071210340600002e0012480080803070020340382400301c80020705018140f440000207081c4140c01c0d40a141d20381c10341450844050058007072010508036020b810607140e0050301c504580b2002840e00000308219151310901d11072210100d0786d4283e840c4900e40584c0041201c15220000412015103410048911030030b007074605002d130380086106548202945030044255980444444001c8131400c0499017100381c0d400e80100244c080d8205482c000140e015410b041a901c894a40da80e00c4126070152240c4451041035000038410402140c02904441c0c0d041e0a01d5101c5001840e00e1060000c100c04103460000d46204600b0217009030000103000710f001d88451840d050900718984d02c4c0c3c00d044100d07440c1308070300000b41d40c0d18120103061340784000d808d018015040e000566500c0f04c1000210016210b0548401d0309420910f05660541c0c0d030565500708001c82824080c0c07950b0f082002204000c0d501d4580701511602c07010900b50203460141c0940d07001f44a594181410080b880107004030182 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 332645206 1250 332643956 332643967
    0xc0f0602011103010e06011709030a08090a0206030115052206030c0311030604110d06030812130f021c170d0b0105070507120302070e0c0a0806060a080406180203030c0102040f050303 80
    0xb00d1038152030442d95481c00318046583c4543c0100c0b118205000c882e01d4124482c2c00740070303500c4400409810081d074aa01d540d03642d901c554103e81d6680d000f0000080d807050b0100010301001141403000c82000741613083c403505140500300101c5950600308454100a023042000300700055250180300f12482c1141000c02a80041c02982c1d40e16100c000c200390b000b0b80d1203020f4110b8034028402152240c840c5000c0c1006001d03202e240030306c02d070340c0203e085094402d5080003081c05602c20b0f0690200c41540a032008643d4103082c2d0a00c006510450201085e2880b0405e90714041440412841074442c4084280e56070b8064040324201210343c0d1522445c1041001e006c10030005100207858429a00030420944001ca500d1070200d251005a812404580f0000401d0104801804001d0120f480303003078440c00d01c0b0741e070b404040c44083c1c041d01c0a0750380001c1c85140804c002c9030349035100e8564400050008102c0c00c02ca83c010030729560019051466580d400241004040b880c03500110142500324082c51810 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 332646456 1250 332645206 332645231
    0x515010905060309030d020c01050108070602030a0c02042a0c02011e08041b1e05041109131509020f210c1206061317010605041b08060409020303070c0f060201 70
    0x40a802414000d0302d000020540e003103020070540e41c1e00f010b900d0040d540c0d0701d1003000444c0a0002032103100c4651054000210b00c9900110a131418403009a0303403c13850074100e0302080050aa404868200d040d184c0c000c2c0080310f10811001c8200f001142c584d401d514040d0300c001001603822120076480526210440b800c1c083d403082d031068009401c840b0f607400c480284081200310f20590743c04640100380c0040b0510240a52102c02e4084807401c032010004040f00c044001d02500c15401070b02e60108500106041d10145680300c84000c1d03954492003274021f901d45c1c0301071003283e214110f840054071000c140c9052295074807a450145240f80705881c000e074200141c01c00214040c2d42c01080d10030b0f843e2800104652203134020b598104c180703850a0300c901c543d100030642c0c010f92843c010b0100341d42046808661800c06001d00040c000c40c200c82101410541042242c0c18a80030b040c41398016110075842c4d015903020006000c01c98050b00d035030a050361428460114100b0294811f02c1503904000d1a040305 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 332647706 1250 332646456 332646467
    0xa05070b06040216111305130b0a02031003020d142e1b08090a02060a0801150c15090f021509010206090609070e06011707020c120c2b0804060201050a051501 69
    0x111760700c1192041088490720010f103a0040c0d0385100201e10b49084100a044096101c0324000070307006800f500349a03203801001905901c01200d00c1c0c0d0503401400420401800c2070b03060b8407003c0f0301803035155800c041d0084001e81050004215001481103c06d04844000310aa502800484424104011030740414070b0000e600c0802003294030034000c1c02030011790508400c1c8440a640c650052080c4c0d07403440c4480000e05821028024040d100040201d4100f0044c0500e801c4e4503d1b9401c41d003c00c08400020b403485c80540802c06040f100e110090b460a40140c4840c9029503154040c40810794890382a00002441c0c0b41000380080040da02000901c80b4484001c1049815903044140c010740503034801b00140d440306107045034501a1010201008031003075000c2240c0c180c0d403008a840034096081c808800d07598032004d840386c6078007044d1142c510140e0410107200079081154107448070740041032901e5202003038119070710100250351100704110340c0040034460150320000388840c0c180c1102a05000800 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 332648956 1250 332647706 332647747
    0xe010303031d030c0d09060c0b04081b07080c01020d0c080313020d0b040f03023d091208160c11010305060f1201091101020a03120b060403080a05070b060402 69
    0xe040e40c0321141d100360032181800d02c20140d6a80d00310380d0f1300d2022042040eaa60040f641c20301c0050303440b28000c035004d0301c602000b03040c680e000030f00c0594545031902d800d200303070f80701c0174104451a03915004900100f106200d41801840f802c0007400050781d2110000e810b088a05030f0141c02c112082d1150000500e07030b8026240c00011798100d0a07603140042c03002c6402c115900a015000c0c6440d40c5c1000f0800031940d100d0015184254241c552030401410b20382c4001c4010303100701d8501d08042c04000d0480420f190700d00070011101c400030035550034989541075085c07407040d1403000240340d0404000000450b03851550f0004140e150001e2040c40d6501c40f2a041080c0c0860541015100c00c00704846a840000350480103900a14828208020704102c50082c038050000302c5d03907040d080111110b150b0000c05c01e13810f80d40c0c05440e1020048004d40640008082056581c2d601000c2840044045864100942081c060b03a4444599854140c1440050084024081032003140100300e8200e001c0f00c181d881c03c1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 332650206 1250 332648956 332648963
    0x100e0103030e030a0f060e0705091504050406061e080d1d041e061220010503012112030c0201050a0e10020a21090b090601050a0b03090f070f1406040e0103 68
    0x84009102ca400079040409000340503240c1c000f1103c14009124141d403200c0101c03c0088101c5c1e148680d02c0c000e11210110880d0320482c205465019001941040c0d0040707a8400e1080500150180d01c848071a6000700c04000240c18000c50318109228640c410090f00c404c58540d82810760180e1204042450058683c24000c3d00940c0c0750b8480302013070216003d5a4124140b420300c1403051603141c10b45074910f0380e03807410191402540d1540b00235101c81c12180342500d082060303403850319607801e102501003440755590130111030302154560880400c0ca02600218469150369001c04e00c1d8035249002800c0d03c2e8013801d0184003501d0650080a4141c000500c0ca0742c5400c012405030f20b9860075031050f2150903020b0085400b203040c40c0002011a0340d6503112280003882030f80101903039198a000c56541306024000e00d50400940030041c0020700c800301c040e5500000100403500701d00030f014045d60410246921480781100e18050501c8940c0322060407004241c0c050700c01030309080c038240001c0201d40040c48042d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 332651456 1250 332650206 332650217
    0x15060c06090d110f1c11070605180d02090105040e0a080a03020405092d060303040306110a080106050f03010b1b1b150c03091302090a060804021c02060d0b03010608150f100e010303 79
    0x10f180d0050710801c40c220100b2098802d07048e558100038107260b01c4840785a03c111030104500303025262000d0305e44446900541110341c507a081078184401005480c0d9a400c4070b2181c2c01d48070b000100480028450080c4c250307009a03d461a2800340284001c0207040c0200d0f000d40d540c48140313107940c2e0b803c1142050048a158041700e4481030301203130a41c030503600003a100c0ca0900600c5100f2405240043c0b481c5529030380c4407115a070366990100c03410300070a6404d02d4403030420801045030629a4002d00051500760041c111a0030002088a2900711003140328500c18410080009280c5025000b584a030400b4030f000a02d052214401300b9268428908154428102e90780030304100fa1041d0b064a1600c1000f4020f1510252a90806000c2e11801c84080380b141704e005880c107400c1000341202490159002e40614144030036141746802425918802580540d618840090a02c030100201100440c00d40440c40c094200500c15501109008100c000c60544581e41081040e03d044040f90441e501460312 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 332652706 1250 332651456 332651503
    0x15050703030b041508011b0804170f0d0f0506100302132c040506150406050906040c0c050319120603050721050d0f030b011715060c06090d110f 63
    0xd4010404c0030004c420b44600040b011404031815070040c03da250003294040000414210111182c039003c8900400b000c003500340d65445d01001101030901c45420f0301509050210000480c011901c011007016503803900c03031003444114141400361094000d6a443e0562070f00b480742407032202c0001944210510090801c80c0d90100000300340b40075003890404807031b08003241801d040060340c80400b514180e05c09000204551100d290600c02c80040300c00240c03203054a0395030b0324200300042c031030501450203000c40c0b00003100008900384000c0280d01390707060000c85503016200c001880c150580803400c03d41441c046082c00070410009843c01100c0c1e20000900c1000b40351480d440589540042c0100a03205919500c10032a800030b0940d1010700c1175030303010881e94214400440750101030a080c001d044542d170020032070040740b80503040b03041c807805401107140405101c3d9061a00e2411a84903441e0f8001c4008265540d52204a50002d84004030090400407100e14205440c1c090b40101c0c40307032503210b4a2a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 332653956 1250 332652706 332652709
    0x506090f0112110403021f12110c0a030809070905040804050904051014010e09150105040506030712081e0708341112071202040b010203161b15050703030b 68
    0x80c468000c0024200070b0080d298543c03450b07482c80d003160104078418503091901d04191012800da91451401c1a0784003014400c1542d80d0600500e208407200080700c00410481e840381c0310410240702118031030350303070b000341031912041540c1001c025400c250785481c102024400070031014015201900c8003100c210006031a42d00c1c00d41e1070410f140b80307d81680d5042001200c003d41021031030078100e81240c1c04100281d6030b92100151104a018018100d201c1d0300b10060142e410964001703a0300c0b1001404842c03043da102c2c4900751315003102c10350031a03002d4030010307030036100c42071602003229480032400080d8200f00140c3e481c80c800d802803240501c41c4010750541ea8507668490034800a00b80c1c0104400010900c244c24491341021910310b10380d00466030b15142c070320701d00fa00040c11012210180e44182c00b44815900300005031003005000d504520003031100f0400421010781404d1420b00c50580c01494040b004180c0030300d07018550001108a8030840754403182c68210040b07c002a0b41361a000608444140 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 332655206 1250 332653956 332653967
    0x31c0b0406050a090f0f1404060b0a05281707030b0408190305090f16140402070605190b01030510030b040606030804080a0501051303021c0207090f02220506090f01 72
    0xc2c8400e510446803c40001c0d945440d6100891510401a081c00700441070600101900d541034501001400340000103008910319500008044000038032850450b40d803840000c801451050003500e81180820341c1c400d040b84d0021440000301411112403901d0015560401d07240d40141c40060042801e40e00007408000062003210b02000c0f1440080100400c01400240200030841d40c0007040c6c400c5c011401404000029021051000204c2c16030255041c800203100c58074a4456058229800f071285800242c940d0155a100b000c0d61031054501a00d403800060688101c40030720350505142c00f084c0402d071b480e60101c4078117076030300442c2c0166540c440d403070403c0061410381d101406102d804100402d8558001c202031a506000e0741c024490340c2c440d0507113460490039000001300542c0c40100586550000b020503072590810740c2c01a25503c9688140180560300a00d0600788070070b6000600000f0030789004406041048611080758545080001045031482404e14a52003805913181001d0b8903031180 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 332656456 1250 332655206 332655209
    0x40320010908070516030b06040c05070f060b0a06080c030a05060607020307080d09090e0a030e18070203120c0c07210f060b10020d050a050a0e1206010602070503031c0b0406 76
    0x12002040300c151641000c8900b50400141114280a0003056a00d01a002c59050041c0e94210300b09039203e0b1a09030812006001e44c000040c1032000601294020500360149209424000d500c04075000d0212010459482c0d40e0350000307414030000c01d003803140d400c0118069981c80003030b20070b00042e251116000591175001d5140020762500c14054045402180403030030081002c00d0b51244101182c486e24002c041d95801c03411408142c1c0314805401c0860f01c2021074407031035003001d00079442450a0180c1040307130000403035015016070300008040e80e42c2d800c000348103940b00c0540d000090600203000a1139444001034443d039a80d920303802015071403500680c450981500c0d400320408600c4805c03860064040c0000186451190041402c1140143e0000c501c921740c1c403542d647c80d23524007140c482e01501d440c1c2116200c00d08002d4140812000b40d100e1085a17012000c0320303401001c447d032410500a04e40155a0012070080e041440f121034100b6581090103a148403500340410950b036010041402058a03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 332657706 1250 332656456 332656517
    0x32705040b1f0e03010e0309031011040f030602120606090306040b07030e010609090c0e010513090c031e0b09070f091d0105010609060806010203071505060f1002070504050117060403 80
    0x4003030b803442c89a402201003881c16100398001d0250992203000c064981c0070300060a034040e001115a0342400c115680520741003e03200d02e203941429184d80c124510300340e84e40c0003218500c3e270002d808081d8030403030319416500140844a10385003102c90008603440d0400a000100080d011101051502d03010f60050510031030700034000c00065582c2c1062601400c1e1140055518440010012a846a440c2e640b1030607100d02070202032801804441c400020490305600351506441c00d400800080c080803803c052098500c10702000d81c052500703145c0c0c41840040d2104005611001c1c3c20008010010004001c494440e4070000d020044c02c2480c1312806c0d154800f280da82d503e800000b040b02038000e050142070311801d03568442c440da502801603035039209406000e00f00c00d80303211204603402d103950031807035001001a0051050307040741c5001c114182040c0d42c00001680000d003060089041500c111401801d00c07416107580e00100c6241e03c1d80300c03140988085c04004000c10f541c42d0112042c0082c4d0400d515 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 332658956 1250 332657706 332657749
    0x21303110d15020a021e070e100e0f150301090804140406030c05010e19080601030b090325030c0609150b06070f0b091e0714041e020c0106050d0f032705040b 69
    0x507128507a0f40c60f00355034003808a41d1040000441e002702008a0088107a481f041888070700c070349401080090102c401454000400c1d080340c842075540d2028010b0480f041d22400d50b01d900e4904052925181840081ca4076010b1391400d881000410200340300c0038104c40d02030070810521402c0801068081c1c000001e0040c18001c500b03400640402c00041e030604aa025443c040503a40340c42143caa105e101e84050205100145c1c8100c8a0381c40144038001102c0f41b1a003400c0324652070750f03900d1030203a40d0700c04001d5414014505d40d64081512a018049954074200c600700e1400c1ea25942d10503041c02040740192103000080c00048a5502c10480142c9004826014090001600414654440f03950082d50719151783c01e07904146508241c05610305500b0b800140107004060380c104000250440c4c19004180c3d92100c4000483da22107009948005000b014403c070b5074070135810080c0c031402901c0303604070f10f00705c81d8100c1d43c02c0003011140174425500d007100c021903100803090009284da0030980320b101c41d00c0c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 332660206 1250 332658956 332659003
    0x2071a160506060306060a1203050a051b0a0201090f06090e0c040308030a0905010f0608031b0118030201150608280b1806042706020913021303110d15020a02 69
    0x2441034801d03d8101e04803a0203680307080c28080049102e03c10b00840201d2640000c00080c000c50151414201c980381c0307181400f61016001d002000201c08a190701d070081d0310030380107551740146070b100a009001d4000411928040c0001d00d850401d1040130300d41440d540c0810403d150031000c442c01182c102c103061761282041e82021008013102e07402120190703e0004c002c2c15a1030a80100b004480781c3d5030155092200030ba0041c5007a41411100c1c0c0804d550320028010030a0018081440880c0254000140d540083e5503503411075480c1e17040304041c00000000c110f19100d46501d2240042e509151070404a040c00300c00901800308980415032014411044802381068842c01511406040b6828010910a12484414046400a2052441460404100416007640041140d1040074100c001c1000d91410f801089030020a02202c130403542c00700400a0201c0c0b00b150510f0703003904684441c50b460312991004c0c0307410100110b0580030340c2c0104d00380851a000340010503141011040044c103c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 332661456 1250 332660206 332660213
    0x210f021510030c0608010603060905040b04110a08011a0103110c190c050904030c05012f07020319030908060c030c07030c06020d06080105010f06020f0601061803140d030c020a020102071a16 83
    0x145d10034094840068500b8038005001c00e201d0050310702881d0001355038002c40c0c071070b5220b105801700c103900c006800a052000003c0e21001c03d12a512052400c07a03002c48500b41e041000600b038a0a458481d050b04c00240905400f50901051040c2142c601c419070403815105d528207003045090543c8001c0e4002104002c00003819000010035454520550080052001d41c03074605100c070b01490b07403012045003d0761028802c070401e180100709240c0010100c945055000301400302960f9120800c4001414825040101810801c01e240d00710309250452401c51a052100741c041c0d0050440140c100300c01c402041c01800200e90441e401c82500031300074070040f40c58424103400f0b00710a105d54076010003540c9000440307510200394035620201c42406081164a00724085850000d013800401d500c0103582c1000000a0721612148070205517000070b460381981c0307208080c003165903800c0e50005542201ca01d0600603a40418a00d0549004100d01e9150150241e0f03030b224035000d0102c2944004410010384400e1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 332662706 1250 332661456 332661467
    0x3090f06080a0b011e110a081b010b0a0e060411090910030b060321090f120a0302070e0601050d0c0e03030f040306060603150308070201050d09210f021510030c06 71
    0x1409600b205115441c00000115542c0d142c21744004070400349904a00d040074454803000304000120310032180129840c0c0c8482d2850340c00449045200400300b00c440000700428010b43d03170b082000300d8247c0190b52900c003944e00f04c9200140600e02c2281d03245109800911941c095a4134400d01030101c002a2600380c0044006d000c480c001070701e054461400243c224580010b10309001aa08210310300a8511020390000c41e800140d40340f540320740394000b070f5003251b252220070528071034110000b000c50210074100a03003004a190030002040c1c1341c175020000c960741c21008507849107240e0000000c03050404103089031290003203600c8036414000051120422964800a0300c1500d0050030104036a40d0f0386d0b54150200e0720a020400e1340c0c0740c90404108041400c201c041e046007801810321a1401d10500c0b040c40031190b1100049843d01c42071071080003105140720391040010240c3c2800e00306d01c0c03619a40655502c0e43c0071103016402c0c0100c0c001580b98207900c8007100003181d0060381c40c000030b80c440001811 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 332663956 1250 332662706 332662711
    0x17100501080d11070506040b0f0403021507060605030a1212110301120b010f03030230160b07030504020913020312040f051f0509010806011803030e040f0203041e03090f0608 76
    0x6400070000983c0c040020501004440340281910f04d482d1070817020600710742101041d1a0186004d000010258076421504c0008510142d880340e1744010524003030045441940005020350721040c000000074440713505500c201d08240c200b641c12002800140350203880ea907151400b002d003003c00005004601000f110345a01e10a04c440031080e0f13213442d880340301e80341e0520000c0c0060b8001c0485903121901d21a041d42a10150b44a6901003107801503c0d6110394000681c850342d40300c2e8520325406000c05000c0142c3c2201c12480c0c02e01540c107058000401881d80503100c1042a25019003990843d5001c00103508422038848059440c0d80daa100f55840c0c0c44082d20645e40176008500d1440005103425040550035845900c0701414040403034011101c0c400d008201078103001100f010004040102d1144000075882941ca4080243e260014001681c00008907216024014418000043e0103100d003d0560f01034089070205551550030110b80310780c0381d80d2019100d02084200890b40c0e55100324802d2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 332665206 1250 332663956 332663983
    0xb0409060b0103230109050705220501090506070f061a19080c0619050307051b0a020a0b0c190501110301150e0619030902030106080d0c2108011710050108 68
    0x113001d200400c1c1e0600d41c51507210144543d414401072003c40d100340e02036a00008549000e81c28800d51660020720700300c04510300070001d02c1caa0410003040d13910200c4078015140a0b1445ea003041002d44d070703034030340380044100040c02c06884011841111000301c441c5070036900001c02004120185441000340554540101009401002c0c60103005051110031a01c080d1140080a0780302d103c02070044a0300d40000d441841000303810020500340003a02300801da80d00004401a2150100610400031401c4640d0301c81050407100340107104840b90081601740fa907600819184021940354035166004000c040705e441450500030002040d07a10241841d407149109940300c03002680d200104100740707401641d07401103903503204140189a0b1846a0085500b40d440540040b60590b100d00d80340d400c11206440000002e8624058801841402c00040804011002c0c0c2c2501542c08000014034404050191100100716035684030f1050000b000483c0078a442441c0400555860b142540d40719400300100e80d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 332666456 1250 332665206 332665211
    0x50c030912121209060f1b0a2607031505031905070509010806041104110702010e0d06020d0c0801050409051c050408010c0906020d0e1c0c09150611030702030c0103020304060b0409060b0103 83
    0xb40d400b81c0180e00960140096010421048108045c031190552200d619230b02000740d00c296025148810385080c400c000d090002c943c4481c603068400800302e642511003080500541036080010340c50120310881c8a550044003017071310906900380103107000001d500054000c64100c0000a00c21350104915000c0d0f032264907480e01c0c4008103401c11081c0c03480600c0e03a80d203190301001120015802800c1041c1094409040d0003440c4101d915907004980107801c041c41015203d00310142055070041003240904021502042055143d44810b961040185601200700d01010500c456240c050820f607001803610100900000403001c81c000d010307516074403918002d4811310400c02c1c03138140074807842e18000e40701600c2040160000c01100b0700d0005044020f44420b10f8a000104d14a40c15005142141c02040142d803111860150001d02c0d000300c402040c01c4603001031001d0381c0143d0700452240c0d400e5200f46030140c2c40351628181403004000c401021584146412001c6007002042e4000c1e550429098808 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 332667706 1250 332666456 332666461
    0x3050c10050c04091e05100603110705060a05100f030305090907051204030503060112020c0604020f031c0315090504030903060506041503022709030309010606050c03091212120906 79
    0x14503090750810b44420301c0468051009020075076856101c01c07041c104d030000981d85010000940740c100c40c41901e600b50078031940c503c1403004503010f00414043d24090755000b0b25000503915182d40340c0c0e0001d00042c60868a40c0045105440c0304071407240508840da41c0c452442c1c1d0343c0e140183c015484a40603d01403201000000c12041c0500c05507902186003103091005a036a0b594211a140c0c07009010ad0305000b4100021014815248094032070448900000e21030750401340108400f0343e42c111006403281e884079510300d486c40d00707a8100810090380d50501041400c40c4040c22292203c1e46e410100c4038528007002c1006047d0711014442c12a030240c2000c101c3c07612007400b44425100c102c0c0d14081c814081c0c180070001810420707506800c4101e0860511490343d2071032081d45e01c000050f80e88824039070012081c800800e00a2141c84014052030901504d02908542d0050300c2e03000702807081d40310b19445e8420030700306070041c0f080c00c0c0c01507030312990741d40d541c00503507022000180c068070410002e220302e400 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 332668956 1250 332667706 332667733
    0x5090c130f14090a020d03090b0714060c09100305061c050c120f0d05090d050307140607032306010306260106050907090e0901090503040902180a0308030714130303050c 74
    0x42250240f5081e4003c0d0495015a0b000d00000c0c080c44241181040300c1200001500c0c9210405815181d00c1303452243c118038115000c0502d0000d020b000055041c208200c0c585285c1e4074006103c03040d100d10300b00415a9503441001454440c003001071245048041d142905c10400c2c0855225070001049035542e03444030148070210395907824006000c1080d801a00380785902c6004601514625000512401800e24590303100d030b06540144008170703502e046e21038550460030002e110859211982e480d007040300c031001004900d020028111456104605070003c0345143c0d00c241c0000e8098000c85d03603080c0103190ba0202c25000c2510108060425510300440410300e0300d40402204e0040011741e43e41c4d800c4500b031480b8000a5107006d0070508540d980c031004140015414800352000749070a20005071151840e10504400300da0003183c1c1c0744215103443c01800003034801000d42e6002200380c5801850740712a0607007101c0354482c1c003100b2012400030081c00010954400c00412a4044000c1035400c2240c01e002c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 332670206 1250 332668956 332668991
    0x11b020d0809061906091103040512090303072009070f090e150603071e09090b042906071b0510051603031505090a060f0b041805090c130f 61
    0xc4080740503401410104800c4008860483d40c41c1104d604005101c60b0341302e580c202250b1b102d54904540b42000f00400060040034003040300004d9000145134a448200310000b51640b04402005081c910304001d00d41d48002d2607043d0161000002c1c06510321030400a4014201400c400c03d4130b000600d0740900442c41b82c91b0105068081c2806203283d110340410b103010800d080d040141800c04000741c440010643c41010040124a0022501c40f070014500b0040e00405482101e60394900a5003040020a01903203001500c92080d010800310040750300c804d40c00039045200f40d09029000c0d10359641058000c542c1042e04400301c410407075140000d1500301e1000c0e07a5600330b00a044c00b203880c03000820000309010740c100c400c41c814000003020145031600300150401b40d06803804071045554001c103100305126041094040d01105036414149454181c5000d44484618008407805458901140580c3d000704002c9400300801851703401e80d04c04110880000b00342c019403c207481c40c10600d28540150102 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 332671456 1250 332670206 332670211
    0xf0b040902010c020913050a0602090109050a080a110a360603031706030a080307020307052a060c0a080a110c010c03050a18050a0801060302090a023603011b020d08 72
    0x1a158039a480f225a000c10030302040041100399150440a480800075106001142090713200381001030710b408014000400030b2015400081c015015500140a4800e0000e98104c01c02c0e40300420f0b41c1000b075120082050700601382e010040000074406062040c540a0140b5003402944406001c00d4103600600e40056651520014010914204500011032440c05803540e220101804681910300290307554407469000f11003c50040e04007165503410001c050003201d41d60007180d0180c11015141e034486841051050301c0d028451000004c20840d010320521620b8103154000843c2901c035103c59501602c6040014901103040c041d51090000c55030058040c00398098250355141c2c04c110701c11105a41481c0b49040101c0d81d0036035000002074595510000c80c018226000c0040341123440d610500c02c00368000303801c0036030762070062050040129440c41c803034881c581060625030280405040f03a4040c0f1289440715a055400c000161031018440181303030508854a900303c40d01c0007240441216054000e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 332672706 1250 332671456 332671459
    0x305030c0c1f0e01051f120f08030703050f07140301090c0c02030a120809030a02060112050313180c0302120601051303050a0305090a080109150213180f06060815011b150f0b040902 79
    0x1100050006200707c7c0c0040d26810b00c04d04a1042000490b00d40c0310f4140c00454a0300c0000ea151020003a11101601d0a20342290050520740d26562104016030400d000c14025400300d5651204207a46852003194440d01450700607047d505444103905043c0d5091780c4100710580882c09410100b81c0005d000800c80341509402e501030300c1283d0030402c0d4484181e841040c284d81c5803000744060402c00c01f40e025820002e02e0801c6a00380e10620490303552064862226184051600c107020034107054442d03605a0754054002d281940d034032110012129840100354101a090b8403e85940804054120f00100141c0604580d0b52101554a84040c0d0980780c1414004019440c182c180812054081d0064240c5040c44d5481c002c04648601480c0e40c140006811416444d44850b802d400a01044c0b007118040c00300381c54090454548020740001a40c0801503103810005000f80382d0750030600e0394174000d440540c00220041700c80d0954030180c001d051034110090f40c8910304104600c4501e00b601c01c060310182d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 332673956 1250 332672706 332672761
    0x8010605061c0f0902090f010806070c0201021c03060f141302040b070b1009020a0519020a020108070804050309040c0507110102070617090a06020c060103030305010509040305030c0c1f0e0105 84
    0x210003001e0703405000036030350360a465503c03442d00c2c10046e1307905200c0d1882110088030600d090f42c9000400c500d4a180038100c0c906000c10700c844200540d0703022a0200881759120a072003512902444210000d001540c800005040650f4001c03400c0c820782d02c202c10001c0f00854041c1c075820428041001244220701c02c1c070183c41c2d010800c6a001500350312115500100c03406032058281d991304160380036a445940250000341c0c0005d640b01a4103800c441c030401d01310344c86c402411034808990019001034806803070034040c070540000007800c204040088600c61a8060030a22000c030420b000030b400d5810110303080b9901e00c04054140800c0d4400a0444101c44550b81c0b078041101000c0244031481c1000f0340103003035074008e44d5840300101c0c681e40002d04c441940e01000f8003040d031650400508658043e000144500902400e0001003503002c02500e42107000290307074540d1880444007162600031001415010315004040440b4600525400350440301087c000a221a5031a00c03a1000300b40c40c05140c0080486 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 332675206 1250 332673956 332673997
    0x2240703090203010e030d09060e0d0f110c1e1002011b050a021513021f020c010302090f0a23270606070611030103030f0e0a05010f050d0905070801060506 68
    0x144a6082441d6a40c0050000500e100c00e08054604540c4203000c021606500d8003006401c11103280701e600324003086000600100c08020000030800604540100100002100410030b040401e02070706109180003403c5043d8511550211910b000c0d00d00d050f948101d210034080724109006010300110080303195801c0c0280c03480712405440079007000010004600c113800d8252401c40f00019081d025410403000e0652888044c030400034404403003401103990103440d0100c00b5507950001801034030f00c4001d0a000d42c0760100c1c039000c244c4c0301a64000095201c080c2078030005001d03036900031000400318080041c1d62144e106100703008002c0d0054501c040c030000c082c1d246e11442aa0403172100c2e00044000d0499284c24410340f140b4040d47c0e101d401c1442038a400000400415411803400b01c82c001c1c8034100200d0a000b61000190036000760301c07508d414441c4641c0740c1d000780c1340b00f01c0807101e030740f03807903003401c0083c01c5050503e1503951016008405156180210103c0c052030f04a043c4c0c0c0025580e2034114090f070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 332676456 1250 332675206 332675221
    0x50a0504030903030f020a0b100305070b041d060625050d1b02120705061305030705010305011809050c03100f060617070f2109020f0a0b09060304170c0601060224 71
    0x30462000400d0860095643c104005001000e074236000791320070210480c103242981461400c000240c2c0c07060000d0b080802c001c00403c074254554042c0e1080e0400e4481080e92210013141d614032690401c2c03400074011400581040301c04060303c20351603004000321640b151381013500362041d07c440c0c4180d01401169131110001882c0c540a240164604070f000d8941c0c0702c0c0c3d00e0001c40c115810a602812a034500704606001504003040204000e18003440e00f40484e501d000401c801030901c6d12508080c66448500d01011f00c00200006a041c1c040642120010300c0e031000e502008001c0c4d0b0f07070030342840d50418100050b081d204030070f5046021507090107240716450300780f000e4490201c0e00703403d6800c2c040320388c0c0540c1042025071050158030040d4030010074120002d1040181524561150754402c243d06c0c181802003c0c4c1e030405039000c0300c00507150143d0342c1d00c450500003090303000c42e540c0c440040000645019850b1010511034100c0e2429021103d031301126400036540c2c00d00c1d0340181101e14803000006440c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 332677706 1250 332676456 332676467
    0x30904050a06271a0f0d031817010f0501050f090a060810020a1e231b031b030c03161406010605090f0f03030706020a050408100c03050a050403090303 66
    0x520041000915280c0c1e810300d00714240f0422164402250307614010b04522a850300a0080124103004501c45451150000980301503503508424042d1444664000c10103000e07c90a4140340c3d540034207000c113113680320b50f03032024042d43c1c010303001265007000500e0b035003420540987d5041e68002070001950a81800c14409811030042400801d03985407503000502c040144105480328164120250b6110003452014003841640001c0c005920b0780012031b0814654054004d62200131442070060440000d5004c3e40013a001e81c2414051a02070342c5061440940000020708003440b50b0048548419404641c5a0710381c080d1025120550300104030514002501d000316101d128465107088400c0c6c04007030f061601d0100240c0022000c50b10003d0f02a11038501245100f090140484080c0504055000800d4482c05140ca00510894012411041c11802802520094001c210480e0003000e6420303924400b4140106107080801d1505000c942054a640102072055030980c554002c1903241d0360f001c607407 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 332678956 1250 332677706 332677711
    0x30f03061305010306090209130c0303050a02010e010609020c0c0604030804150c0f060e0c03030708040308031305121206010e0f090603032106030f150f06010909091a0a0b010203090405 81
    0x601003141600c0a01c161030310310034035001e14019480041d041c44103105001905901800e0102080d1112490100042100c90720b01c0a40343d0500e403a68070346003101170603805800c0181241c7d40c03650a00e080496540300590203005c02001410854040b0110202070103158450780c04040c04018041105000c070740f0910320f805900e49014500b607540d000381a164101c200d042100d04a8605880c2d9035070303214000c020020003103000317000c5001d1894190f8680d0381d034240e3f00c242d110042140101200040100b044111422102500103054451001561492000070703032011801c2c080c501809070105007154810140540c0026015107100900180d000800c03c0c0c40300001d0203958588800c0001c0400303142040c3d520402420403204500050074030a04150404603c4080d01c04103500001a10b1205080818100d400c040521050790850b15403800484032906103070010261217080032402000c021407142c0e4054510300301c4003403680b10340356880114180c5000c0b0310042e00590040c408080700e1303c0e0907031007140c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 332680206 1250 332678956 332678959
    0xc050a0c05100f0b12030301050105071b1d04030825030f060302130b010e0f1c030e09100e100b19050403140d020d020f060f1801051501030605040e030f0306 69
    0x30742c0030342c1140102c0c098410039800d642d403003600c600600000f410040495040818400003560075581080300081142c02004070190114131604c10190384600f084902d003000e000302d00032204100c8a9190007000c5450207640480c0096a030000181d42c03a00c42c0030340c004034284140941042d84000c050100c01030316044980c17103a060380d114030001c0160348204e1700c8544025143c90104091048030b002410b10f109114078140995901d01d096421035030341c0d0700710f5081c01c000d41d403d0104038080750804a0380b40d0443c4900d5900143c40c4400d00901400300d180e28001c640d0328206956583d0b41e03446801100341c0703991080e61070002050240088801c202507004003405010b24041e42489d9407602c5070b10040c81c0d186149002e0342c202c6030032410507541c144401004139416000604002c03100307108003a660a0300606080e80f00800d900404d560300984256034070801c18074002882030303040c1001d6190b42540c0151031a40824589000050181440d01401d615050250065424823501d190f80000c41e600c000c1034103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 332681456 1250 332680206 332680213
    0xa030509220e07061b020a0302060a2a02090c1201091107080d0e0114130f150c0e0901170303060d0611070501060504060b070506070309051e1606030c050a0c05 70
    0x7410750301c00500c01c0304000d41040008114051a0080240c00d0004461703806000d245e03441038000142e1940f100e40c1c421a941650840e5803400658812a031180b80c1030111400c4100074240c000e03000c5904d081c128010350003240d100701030780c988080310801d5100d0340c4444856124542c004002054a541c4001d6502001c03080c1e051030512a907407101c000380d1051101e49a81d950f40c1000c98800002481078440c0e0a40100e110b004a00f041076006007111540c0c03c0040c41c540c02c8004a008104030107204030103401c680a0700b4072600d032490b103025041c080e04042150295142000000c0d010050342240b86031941100040c500c1c64a13014180901e40d03207011010340e0b189449045c0c861541e4000d10040500601130303400054020308240400050b14284e0b400445c0040007405440042030340414081d4001416007030002e0302c41d155240c070368113003140309680e03018201c0d0f00c958041e42424085a07d110000110046022164481c4410307001c4419403090140014018030003880d405008a24800081d400360044 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 332682706 1250 332681456 332681509
    0x1609080312010f060305090a080a02031314010f0f0c0605061f050409060b0a052502060d0204140907021213031b15080c0a0c0614090f06090a030509 65
    0x22403840e03014030310300c1c03525400c18001006a506020495070260074036250a0003642011300b00c841e61250404809001c5450004900300420300030800c03104c080c0300d0300c5594140e0544d035943c00f07036900401450040c0402c0602168042081c402c40e201d00c500c00498035903041c520301584850b0000c0600800300c1c0c2e0003007000741402004140800c0040d409049035540c0c03564035424990b6460940700c3e42e50015804880034880384041c190885c00703980d15203216804c00c0c07034410324006207560071484030400603402010015040254803110303001003003680e002d4141c41401c060030308103009408000b243c0749401a0044001414a1000c1000424125841304905071050303460b13884410682075000c008220720640980c04200d03000a03448031802c080c000381852900d51600340340107095803064405180400c510074400c6010802a90b0003c03450b404210300c000c00e10700d04107600503540e40b00009000c142c0d104180014a103001c00182d1001003035455a9824240b0310000184150201054900b030460001c1c00714 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 332683956 1250 332682706 332682719
    0x51f090b0c0a0515090d050c100f1a06040f090c11010606090f0e070905090903040803030a0f15080c150904050702150702010608190c030c140301061d1609 68
    0x2400c1e03a0803161000d8950201c0c40c0c070f800c80c40c0150f1100f11141d20350109040000111010034411441650350815680d60f10030f400320309090400303031114144d04914200c4440c0740300d00c00354004801507115401c2d101010400c9010045680198840d40704041182c80f014007860301907030819202031181381082031840c041c9001250075600103412010000b030303640310100640282c514400c001800c0095a180345401c0080b4001c128402c1030080c03d0148800f00c021840e5103000f04115001041c00405581d100e05002080f1000b80141410289502d414030780c0314140140d0700800340d011550020000d086a10001003480074901c0c400780965140c490a0144a000b9284c0e4010184140c000354098903d031080100300e502c94100280c4481c0c1107a14222043c0000c00700001c000e06409a68a840d40072007019262513420003141d904018004501e94000260b0781c0d4424860710a4400100c00030300045465058951401c814049014000301c103040104200710300881c3d0600480a452626080c20790312040d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 332685206 1250 332683956 332683979
    0x301090213050f0a020c06070e01021c030204170118120504090e03030a050705090a0308030432010e0d0e1c0203120a020613020f06030c0d090807030216051f09 70
    0x50040744a00e4031007040103202c2e80640c0c001a0700686110045050000d001082550390500411203401d0045050242070170743c1c020891a100d280c80d400c1c1c00080900d081d900200650400e00c59004088803000700f51b04090410b010702c907c034210403691800d56007060f888540055200c0355242d002d00c2020030000c21003441c1d41c0a91410703049528000d594030f00341510b021003103940c003c250500300074080c4000c0b003a1b80d03104060001100d8000c12056200d4a032130400d01500e4414400926081d803d8030b182c4e015641c107919090f10030030717140402080358805a8900d1078484000b100c6503030000e40078600216103450309000c03401c4064400c00380003c920001d503010038901522121000381014020603d0751982e03a0401c0140d6028104040c0802c03803561a03800b10340d0820300d8410240c070070580400041d0310fa8000405403245200711490902c2100c0007801c0103c038641c403501081d030040c050348400d5406400b41128a000311000642008000d12070f814413052403135801d0342d14108018001c40d00040071074906 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 332686456 1250 332685206 332685229
    0x1207030b03071d13050705010f020f0610060206100b040603020d0216030201150b0c0c041d06130c090506011202090103021e090f0306040f0f1e0b070e01020102070507050f03010902 79
    0x1800003400180010b5400c1580100800040c3c48140411004d800113001241c0d0004a41c800c0c06c001040104040301030341020030615002941e44910003c000303c1e400350550b0031044a00980036a2117a45072000c1000b01c542107800742d40b00c650420001000100d10070350084c8020b8850290040c1030941410842034103080381041900180e444c0d04460440001c0c18000900921841215905e0200131607035180d120300080810504c01c903036070f0303041504079240040360030203410000055408034030f40305d003002c0407210410b0029074070f55915040224000a00d8032403e4025403050f19040c40304100d121080e0080e600801c1da0700c3c10180c0034088602412442000e5981c4080315961064403500100140486032404001d111310a40c0712006104c0403842c10415100741c1600030002010302d141c0ca003000e982580700c8122151242c4848601030050010360203015008041954482c0b03110250300c80128281d0142c581e002d4140d40117800c0070801460843c0034020801c402400200d2038483c1900003440240c1311 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 332687706 1250 332686456 332686469
    0x504020c0d0f031a04050a0b0603040b04060f02070f1205040f0e040218061302090d021201020a0207081b04200309030706050906010e1305070b03071706151207030b0307 74
    0x20605907010780d900844103022801140c80c0403c0300c010540860001c03100c1660300e550049680d20302141516040380c000c1c1741e050300058242c0b552400c00b1314001c802680c0880d0140c62031803a00e01046508030040c001c40e405c1b01d0300500b000300209403c0d00d41040d0103913160030900c14004100300018030380c85c4858502005004102c180103241c0340a0051040d00040844c3d1074222885c04002c12103076a48070490440c8403015400010707100d4090b100401c0c01204030440c081d40c803184041c400d9504420540041000001a9080c0c031805076981b0200d941c0c4513000318203494640c40f1038010728010b00306940904a4840340c0311800509403031000304500349a01c01d494500c3d00703800004817401801000d00030700e03800054610007016175600d885512200c40c60094101c1d0000c1d40300d802442c0500400b00b0805e00a0160300e070f4280d987e400d01e401302030f100c0030302000d200c00466141c00002c2c4803843c202d46084c0c240d5102032402854040503048499040740014005030516651788052a0a51800c1001c000901300 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 332688956 1250 332687706 332687713
    0xa06020a02010e06120c070501140406050402041b020705040b0a03060606050702091605030402060a02150a06140a05090c030619030b0a05090105160e0a0504050a05041103060c04120206040504020c 86
    0x169000041c02070b0743c400c07540f5024500c10001210810380e05c6405552104506240c01d8480c1c0d860724041d409811503448404003ca2008240400e020700c1c0d42c0000d00540c401c460402604140d03141c11400b05183c041c0c10b00c0940c003c1002002a410540c120f0800254002d03d131071070450302e80c0d413040c00b142c1154020380c0c00501e008c00c5d42c1e011801c1c11030506400101842078000c603040c0180005001c2d00c0010300c000c0c020400416880d98040c001c00030b0111001502000610070301c0e01e00c070010010401071140420070944000b4440c15814031044103401c0c1d1f00c028200101c00e503140d80c0d4000c3d071648042d019036000b416003a07071901c000544081c094059031180d0300840c818289605014151400500504241d91402f4107104900614072600c841216440c280001c8800f0350743c4c00240307903410580c0596089030030441000000c1c4020b0388802c0c0b08910500d0001044040842403654070202100c10030f10002c0104000e0080010492507c1c5400b44020401860140c036107002c501a60045100908140e2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 332690206 1250 332688956 332688973
    0x9170a05060727180c0207121203020c0d030c020c040e07091d0303040303020903010b010e0303090111100e0a0614040b040b0c1b0c0108250503090a050d09150314070302090f0a0602 79
    0x40301d401742d90090300300c1d0300c02005150300f480c4039240c400d050258010300040311500310300283d6000b6012740380c042c110002501c0480c1520b91000c1c015114220741240103009070248008545024400c0d40e080e1088040101101420301501c600109500a60f82c1320483e0071540c5202c0e8000c0402c003e510417442680c1c09a103c951107024076094410300b02c4c065060020900081c1c050b61030000c190b0f10b81c40360918143d030012020818560a048190202c101c240741045142d150313480c000241c1c404160b201d0300d810002000e041000c40080344080c0e80041441802001080c089024070710364542020310f80094920b082170407000081048280c2443c515243c22012840b12150380200c441c1da071064095a644060083c60a0b03281c1c03072803c581d4100c01c180b00c0c012000c90704a400401628540c250b104044418007403c1c480302074100c01c40c0d4030400300780140044501c8182c44c8a4041d11020060440790030071503444140043d03019400494170180c0043c18420b170028155281400d0100600c0503401030729058 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 332691456 1250 332690206 332690249
    0xa0b04030518040603020108060405042f2d0613050907091d04050c040e07031b0e010609030309030206180901090e01290103050606070605040309170a05060727 70
    0x42c492010030312451800d0720810160340c001100302d60000c1c0445000450380e407503140c030342108018441c004084516074410400b0341c0d900c0c8031413100b0f0305000302d071a410101c0901080080290b039101690aa0b18100b0324098540d051007400ba051941c2600172550a06489901042c00300e40300311440000a40c881c9410000c1ca088031b221020024800e50b032810451601c0e8a902d030781d40940d200818002c03503070b0b40042002c4070000e0004001865210b00d66480080d03014048529911560050b07070401d004800001030b0b9903015402d1481129419105c00301500c1c619000c00207940c0000070031340700040c40102c20381c010b0360351101c5550180006910000380c41c41000c50803400c4403414035482840d01400010b65000000504180c82001024a00440c5903911700300441c209015003680141064100741c1800101900504508140e81d4049840804c0080128030700b56a1031298101078240d0300304031b0214003054400da20711400e407440d148000c5200b00301c1207620b00880f1400c1d4800c00000b8445500041079 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 332692706 1250 332691456 332691487
    0xc0d020604020f01020109052e0e0607020d080f0601121e0f11280314040b0402010e010e010503071404081009050c0402070b01062d1e032c0a0b040305 66
    0xb01d080c8000c00c11400347c0da40301607943e2104207141020711200c843d600d10520a4101100823030034641700602180c01020302e8030703680b0743c01540d5210250041c0c12003800d502e441840da080c071031002c4001c0c0e030100752204d0005480714040300c0b042e5510b654036851550340410aa10203000108420360b00068050204005002240c1007000d44581d010300821080b014036540144901054170248000c50501e14090401d40091481160070307094503282c0b102300300501816048461050b4000c0e03c0704e4860395803140044800c040e00010040c0458414008100082d100b58002062840d80f204c01da45000d49402c1520300d0300102c0610030b8030564a404000b002c105052002c000d1020040da02036042c803180d139540342200c22050142c10200f040c842003110f48400001107a4121104003e414030210341a1007004000000c04414000282c5007234840c3c0300060b02c43c2c81041c4110190803045100d01c001c800c03003141c4600a422014030079108014a00d03000c00d8004007201c0c000c2d44640c0340c10390350b69035586d03401e201c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 332693956 1250 332692706 332692729
    0x30c0d050f0403140a0f0f0c050402040b030a05070201090b01150908010203090c091005190806160f200102040608160207030b0106031d0105040b01080f1c140c0d02060402 75
    0x1000014028098600403140558080d20f0b405180c41c03c603080300c3c115041c40c016175564040d004558003c01322040c010855100d844071406641e1007001941c1702c00c10700c0180d1040f84580f9144850400000300800040da0241e5004442e501c00415240d081d515440700d003410a8021010300480503024409850b00000c028000703141a0000354254500f8180c1035440b40d00c101c074441d0050981400050f017101c0c0009c900c0020340340003881c4000c100310110005941040714040c0c004188205c4010071804500b4214000096045594507100e55000c0c0e2400c44844110440b10144a45500240c0d02a003500780003502c060111552040076614122085100c1202840f60f80b00940d00600c5c8240003044410510301d041d00c0441c1004079508241518158045000120001c07455103010241b20800080c5d11320300741242c520000b140c2c0c1100000021603202d8036000d010034941c26240c0e1510310120300a04000d03100035940f0200c0c1b0b09081c48201d46508041e5885a200016004403003004114a00020400c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 332695206 1250 332693956 332693983
    0x150e06060619021e0307020405010918080d0207021519261005060c0609010b0f03031b0a020d050109210807140927010503030c03070f0204020d0e030c 66
    0x54241000801c015100b4004502c1c4264501d20301c29034914020031038600c248200c002030080307410800700055126000355004034403e50402c0000200340c401409100d49040000001d0760f20040c0301da983c030a85506ca10061074941d40c003405018096520801d0030301003202d0b109101d507540c500196013000300034042030820b41805552240043c0c0c03160b241c20640d0348440c208011160548170480032030f640700707100e41c072a41c0d0150000034104400f68000c0342950046525900038894401c84008002461620240d1f00360164002d208525403008900c03441100818000155007982d030f019000f1818030440d103207003074843d80c0d101e030422402c1043c000000d4a0204182e050486160090b00009050546c00ba0102c010010044680107a00c0503820440f40741c40e6009010380c80e03805420543e85009294699072440940d2480c00000d010306005c0b044540082519018515060180d07072401102d0321852016a0030130b0342806505d6080d4004d1190301d0700804110001c545600c5030000e0a40307040d1241151a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 332696456 1250 332695206 332695213
    0x21c06060503130507030f060f0b040c0e06030402061e0a0e010201020901081503070b0a02010e060a02040501090b0f0d060609030506090a020f0d06110d051e07020309060309010b0d150e 81
    0x4000d0a50310030141d0390040403d001c68111400103050161420042c1c1d00040c01c0400c0f030b40f00100c01c014256009090b8501d041c44180b15044e0707100d04002c11504a50210307400302d02e2081d035418440c03910b1002142d02c648002c0840b810680e890b005801c04095940300000d60600010311040400d80000400d442003409100035854540a200020641000070306503005856004904421030365052140034050100c00d0b44442d118500c0032002806000307040203000c014091100482c15590442c000c030f40c266030041c0c4400d464203240c9960303180198403440d015880c00c0c0c1c05004c583c21100c810300030703080141801d0703a81059141c29401e0680c2464030180c21403c8541c0500a1080161541c51580300741c14002c4808012b00740d030900b018001b604908508603002d84c800a00901744040e280d110a0140056049102031040044c00b050a00c81c0141c4000c4050703401408070300c6040c03401c81d00a40d804841070001046240814000c554a0b2646850880300402d07150f4a042000b58180700d03a80312a02402d004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 332697706 1250 332696456 332696459
    0xc010c090b07080415020f0f060714040302150a0c0c0f0e220308070212071a0612191a040c0905090a0819030212040b04030f11060601031a0a0603021c06 67
    0x40031290700c0b80344101d4203000d485d11401502d1a000b440031050040025050b034031020701c0031086540780e910484416001c580701920b00d00c14003103030390141d13001c3c2c0e0303030260104005414613101c205e0182c0184450300c0406c00c0710b40360b42d000160781c12134182c01041c4581064005074108030800a81b100014504182a1800b401e8030741080c140107034100c01c15030541801c0101d9100c03880e0407410b00804480c068690300d0001883d50412003200d580702c522820540d0b040e0702d00c2c0c0350f80d020090001c0101140840e1588804085e009230042002950003444c881d00304180400c07050020112440005c903015140403174505c1d01000301016502580d035018240714041d010b4020a035555101d58082c41d58170f840ca80300c4074625242c1c0327280254129800701c0b04000c100c103038501e41071400c6148191300312012800030340d960300c0d10320266014a100100e103500100143c80556a210011001888841600c2c880c090000120141c40d440390030503100035008940d405039a0344481581c50a0010a0036100300c405840c0080 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 332698956 1250 332697706 332697713
    0xd05120112080901080703320f040f0b1005121005010b0f07151d100b0102030a08010b0d1d0304080f0a021c08090303040b0d0e010b011b170c010c090b07 67
    0x486022000c2400d020005d91102401140101144211001c6a640c0c0396205160701101000d030713903500c2d0f00c08400980700c0d6641640300003102e5025a07004022058035100c00000170b440e40101a800203010304c0144500e95903200181c904403044c5a4100b407604004117004076218907000d01d601420103a00f100c1d14021803011500424414414080e010001d0b0545002540c0c2840c5c0110415a14242a412114015a21198903241d003000c0054486140903451020382d400441034400c521603030b840f485450780ca00f51480907544d11a02e0319100307041c4e481003403054040482112074442c3c8ad00c5070083d500e031800c002c0228a0082c0101c082200c552044004400590701c40c4d0101071011240d0303a075000300a40c50302e00100503021fa24101c0f94075000209020a4240d102c00c0a05000e87c0d480405103c4400b510341c0b49400c96a85c16442c0d40014042c01e05400c05015548104c0c005070300c5100b10b40000141d007240d18000c0d810101242001d45d44840c0040a142c0c2d000606070301504101c01b906180c1441c070f130b5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 332700206 1250 332698956 332698973
    0xb010302011d150f1b24040f02090a0b0d12090602062202030a140a290a1116050a14070605190302041503060e0702010603110d060e0d05120112 63
    0x320752140400000550507041e442c13110548129030008445480200f54141c019500c45030704440101c84071907010611b0103074400a000e00c0d0b00803038200d807914807110855003d000350000700030084684292200001c0c4490348030440004002c6004001c60703a06030340c5440c0c0003400c10344140e000900315400a010300c903806010000d01c5040e603110540c03150078500701c6d2001c2410f001c1c5222004e440420081405034041ca40800c508800c070344200d00403032100c009104070300c1844100c5030f40e00141d904000e00040c0107602d20ba0043c45100c0e00e0b4202c140c240414120318031000074500e203045031243c112603100c10810505c04a11100304440d207010f4004142050320041c22409200651448080000c414a25140c0a64106c4020b050400d00d038800308600508050050070507441201d0070161240b000a0003503206100788810740c1d910003c5144402020410003101121540060360520b0340c540305440e00c10f0f400c001400107030300161101078544024001c5000f03002416440342c400a02c41454000010300c600 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 332701456 1250 332700206 332700229
    0x70306121b0b0901052d0f0a02060109061401080a0b10050702040507080402030d14040b0c0c0102070906050109120503130e09150f01030f060f150e010b04120213020d090b010302011d 80
    0x140c40160361b11501c0507490b1000c10035030001c403460700400181e0708401d6026500912403c5019000c40701c0c0c030b990b60b800440494525216040e0b1005c40c028080200b503105201c555000814482d020400c180030700c000500d0b10f0003203108507010400014200301142424012250300c00f40c20b082801280ca055008240c6030018032006c1c13810024022040f02d1120040010f9801402c00c006405446220440900e540c0301b061113080c0b030161003a0b1400054021284c0940420354406a4030801064901075041d40c04c3e10544008a0f424001844510002a02040c0c034100034420100200e9481c24103900090810078680b03540b00c0b942450104020b250002442c40d40d044a81c003a00006147d5400d0501c1401401c03541401c056080c01d11080c0003228180c1c8180c082550804111082030381d1740d4031445400b5214a00ca090160700c0742d5450b01c40903250241d4128026000d00f45d0251500b6034500c00c1004486031240c00311008031000e0014003e65a11490410700090781110a0400d01020070000307a501160 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 332702706 1250 332701456 332701477
    0x50a0818061303030f0501090501030b060904050d110703020d0b06010809071a070312141f140d080d02030c0304110102030a120e0a020315011401090b12070306121b0b090105 76
    0x4100a0b80425200764000d074050914800100070383c3d40c44181d1513000c0c000a2005503003401403a40801c20519200444500460b884801002603c1c081c25007038170509412450488130b80907040c2d00202580760000c08612840c414802c2180a240c139100140c04041c019049011662001c2c030244210984202086840c4003a01c81d056111440d51404507440703000518100d2109003050420201c1c081859178003401500140a80c12000000034426401941c2522800c260411000621700c5a400c180c0400300c080c8d8043c0100d2880c001c0d000900300e050368011740e2655442c140c0042040280a444111000411400d1010f181f410300040c0b001000c07204004503030a5040c1d50b5039000403c0035810821910034550160641c4d05065040c10341c00e803041c00c244104118421095401c400e213611803c4c00e0b505a44010414504041d130f014107610001c10014040c2051565501001c1103407060045440782d194803481034561814207070001e81070300c008a60300596940343e052200a040307a0f0004291255160b0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 332703956 1250 332702706 332702731
    0x8070f0e0c160b09061806010e0406020c0f0703060b1f0e06090418060c08010b030403080709180c0e01020303190e0c09100303020106080a02090c28050a081806 70
    0xd030030007940040e2007250740040541000880c9441048048010036200e801c50380c060f56a160390341c2188000400b12110002c10b550030000044c807207542114003e0f034000f0f0007aa40107041000d580c030041c0c0380405120a40f0341650003a00c0c2001008402d003e40b04030440161010700060f0358101d140080b5003c11603d41003071282c40b101c0d50440303448040c19541d00942c018030501c004802ca0300c10803034428407540c00303036015070410031042002d900448101c0e0407215035110051840e43d460b02d00703c80da11005007140080000044001802c90400c0309481100544080001340e4900c03000d0010f00241e061900190643d00148104140c10a0b01440641c01e0488034002050310705070a244075040541607a5520b41c08030301c05040c80780c90441c80c1c2001050304d100390001c2101c035407580105a550300880c0d0f0000e5214a41e600000d100b0039659010344807540d00c10003420001041c00c2c1d80024656448060b4900003040841c40c03031450303940150700c15009402190104c80321041e4000083d00e07200000c20070002d0301d9 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 332705206 1250 332703956 332703961
    0x1e0207020310020310060801050f0a1208130e0f1e0601030b030c041a030d020c090a0c110709020c070b040b0a03020f040e09010b040b04151505090a0308120108070f0e 73
    0x4509020003402d40c0d1450804556920700910742e500740e900c4030300418000a803908000706840c00c2c0143c1011003c41c1c01010f20340e05500d0414420001d204698048401400070300482500510b8502194040c0580c00000100341c035288100c1c00091100400ba0100003030300860190444018028181d040384083c83d000c0baa4100b0840032030b20f011010508950018601000300608242002d04880b403140d04030259025014400c0080341d80700e150904041c1d00100c5040070515418813948281d60180741410700a800d60752030841941000003d0b8003c02006400007002e100f003c20600c41d9402400c003a00d2103908060a20180d09401e019031400442456800241e0004130b11002e01920010015035650446e585413008502e07010301940c88000e030150b8145404503000385080e001d0b0201c076004004401b04410b107002c0260b440b00c40810806814400304100d18001910344d81c9880c005580581d612642c0e81044942d980c00b00c00c416070201d202a0000e10040c408403181d46203a41c00c640c0030101e412001d8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 332706456 1250 332705206 332705209
    0xb100c170708280212030f1329011208040317161101021614090406060902160506160212031b07030f021608030909130602070506090d02011e020702 65
    0x18851007402500d210303008540615441070140700b15038181101e6030074070040320384440141d946820641a04808440510000c1c2c1c20b824440c144a60040c0b58148482c10164191502140040f0400e075190010280b50800c440501418500f20f00600d0501d50000300340081da2200301a500650100070040c10340780b024214500002c005036921101200d000d0b084070047d5181c032900510300014000e025000d20201c841b03a600e029040c1500b181ca461040304414030b040b10402112841c0100200c4020713035901c0707022a07944c2c0581301500d91204128403910410600e820a2450041c009144091195403a041034a155502040c6019030107451100d05459449402c0310390080051a031420014030310100c0c020081c154070101c3d24001041d26000c0e01c103045496064440c035140c6c103000300001c13948100000c80301e80c1071104105a102108034900420f69800e540c030030081c0e80c020b10007a0f416034083c0060000040085c849004078038a540000c20003104801464291041492140602c99a01140207010b5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 332707706 1250 332706456 332706503
    0xf0c240c0c050a15080a0203070914180a0b0f1e09180610031401050c18030c1c051c02060f0601050904060803041415090613120f060b100c 61
    0x90b081c01081020001c2e162040c030100344441c0c190302c50000302c02d0343c04643d0280c0d55201b1203014403a01d81d03602c8039644c02c20241000c41001c0b6084940c104040000300b1003a0445c220480c0d000c2d00004002281c0000700f04c0c02c11241c4a60801000d1241d69580c1c505810f20600f1880f200c407118050302c010003071f59076020201d2100510442d40c000140a0001005a0600245036103000d69207d034000e840c048280040c800e0132100f00b10703011158280d08000b001c0ba4103594400c955080303580101282c011000b130030003140309424501315030150f0501c181604420000c050000e44843c0c4032075040c1c49014024944000e645204c09440250107080035000f007592a4407601c102c54034801e000d0300500c802070b43c8040715903895100d0720501e5001440c04084816900d00750700010303410842406110b0420340c00c001045410340c0060404605200a520300181d40c0308000d8960b12070314015211040c8200907420a0420782d001c1510b89840340c2d200c04840030800c0d4100c0320307015900b600151113091400e000702e0000d06 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 332708956 1250 332707706 332707709
    0x11404050f0f0405120a210b010c0320010f0c2304031b03020910210206070b13140304050a17030d0b01020102090307030609050c0603100b0c0102070206070f0c240c0c 73
    0x45c9400069038507070480d04281f10001c500d00440003980b03580d040919980484102c040620300140043c602d04010a00c071b491905d10440400740e003112103601c42c482c01c0742100d140100b00c0302000d4030380b00c014841d00d42200254407603c0c4664030544400d22220024a42da2280703000080c008064620703074007038540d00e290454015503400341c00c0c80304501f0700c0007040300e840d0040d1240c400498401c0070368240000c8440404140c1c59805840141412040e40d00d43c0346072400108803440700c0c1021941a03001c520f04080c0168002c4c000000b4685da14207050500c448010326800142aa03a103000420f040c0001c0041224030245041c440094141350180040f030291085050ba254140306940c0f000c020701c0081d500140303201d8440e0048a007140c10302014801d1034041110b08009500c5e403160100315107607038040100003601c8494001440d0074941d0740050595048550207489007075071165008208600f401031000034050189010145441d600a03c82c512403090998070200401c0c500f0f01801c02246044040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 332710206 1250 332708956 332708983
    0xb0411030405010e070510050c0a1b14040b0d0209040501140a0f061a16080409050f09010c0c02030319090f1512410a05011404050f0f0405 61
    0x4940924944051500191000d5400d5460240c1c1da5a00072400948501192805010080c600c0d81034001030380e013904641080c0c0e0a5001d10b19000c8001095002c40800c0700da20154a54406401c10088829144005a4140c003d520345841d04050343da500320b002400c2136040321482584c1c0e03618a0300e18090700088410a154451030301c01c1c06a418210b4220394150181141d0400480c0c2e500c01d050075400c0301c4000301c140e81ca00d0401c141c009401c2d07089000a0006d000756491032401e40e682c503c01045810454035001d1909404080c07100c8682c0a01562480e00d404d850020039110302500065242d10070480307006038510710782242111050007443c3c2140103048010038440302d036540760241c1e5074030a026120031001422041e440d815032701e060720a4001c1c0401c0e0b40038500b20200c0c00144080c8106060442080450360403000c41165888440000d1081d1100c038004546940b41c07901c001380c402801d0142a02c03c0d4140410040c65a0710720a40540c07101c84502a052a52680e00b0702c1c6043c00d00320801d40 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 332711456 1250 332710206 332710211
    0x1090e010b0d030e040e0105220c1203030605040b0102060402130507020f030d0204050405061206040f030e0405090703050708010c05030f040201050910030605090109021602010806030304051c0b100b0d020d0b04 92
    0x38091541000803032134401800d840511010107128103032400c0b14000c4424000c0038110030000b103100031202c61018000303807003000301c10b0312261100c40c43c080c010070304601140080c1d100c4005200b2030409014081d2685820700040c18542802e5001405e03040c4c076803030200d403020b0b9100700080c2024400c01612007140034400c1600c3e6102003150350003020b0b61003401414050303802e0202060b110b08000c85071815240760035000e42115100c0e641c0d4810040d1442005a00b001140d1407003070015566845164002c0d980000107000042c6140b80079400d24109500081859250180784505250000f0490354040090303400400076540700d10040c0c07800d000d154101d0380c10032170031080c40070080c0e05540300c00140e5000309e800c1a820ba0783c641c1c0ca4800d130b1140c10307180d42540120307401880055026116039030300107000500741d0b070801f9211004150781c04103030f1113105240d0b526152510140f01901608a42000020f01c50640550804400c51501e115024640900342ea0004104000555903032012140d554014402d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 332712706 1250 332711456 332711479
    0x1806020102030103170c0d21020f13080c01020d14120906072d120b040e0307030e04050f010501180b19020f0a020312070203010204090203070203070b160801090e010b 73
    0x80c000e4000340070880314242980b60f242c01914000c0103460028011000520100d031400ca400c5450381b150340c80c942c14010044a81c8450021940050601815110180c81e240e14103100741c001c040023a584030301c0d030503002007216080701c0c0da0101da0b0300d41e02c03110b5040455031500c5400c1c0f0000140f06010b0315049001d0050184101d400020448900030a10395803035070010700340e1804600c0d500740000c60b641c4403800034407061401d00b4000d0303c030095900c01c0c0c0700d8002041c07510100801c00352511000590781c141c100058100405800c090581c412010a4400300b040b403800c081118a00d04040c021a814861001080d840000d54690044094011904d1403510f40b01e000b0071b00b040702d100424000303015014010f219401070b900040d031140c0c01c0e41c00030028206290304010b650034035442182c060b07801d95020480440c000210f80020350183c071140e801141c0c2d5a4040c10180401c1c04040c100b03042070400954040310b0389502005082c1034810321240058040d240410460040c41c09050b481d40080c0c80c18032 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 332713956 1250 332712706 332712719
    0x60906020406260114030c0d030f030f0213030201030506131401030209130b061e0307030503031b0309100c03020403020409030f09080d02060c071b031104110403050303040f0318 78
    0x28108641c010b071545900028080fa07200016030403941105003122104004120501c0c1e2403c1040100c2005819542901ca070030300420b8085401840039408502c114503000308159140c0b082a004d0b0750b0a04c8114248031001e09001d80780c1d4a9403001034109a194004035046035502d0346c1d40300002202420820060841032040d80b0085024801a8810742036080080d620303400501e48020b84907404108403c081c0c4e20441001803e05d008881c56a43e03050111444215460421988019600a00c0211745074900341c0320344144a080c0545080140c3c00038400e02c510244001020024032179040c20104c0c5c3c82e042800100c00a006035800a9849420306104a092581200b5000c604d8901a030303402402075107036041c242c0d8419602c100c040c01070344108001100c89c1d2044002d0402c461081c000441c00c501c041c180e440c120301f9260001d0310440c4074000c1c00000e620746445040c1c0801440c02c80d69060614580b035103600c034000180003031b1960100c2009003041500c10064424502e8190409002c3e940e15682d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 332715206 1250 332713956 332713961
    0xb0f06071716020906090c0307080403050c1510061b030309020d0209040b0403020c0915010e060c010c120b0a060905090a11030106020c0306100506040b18030307080a08070c0305090d020d060906 85
    0x10b805034003901c0034401003401e41c1017055800f481508030748841e5103103896046080381c40341c600a000385c0030803405000d4038000b05001d000c4c15480103101ca81519050a00d001601030710f078450790064060101c02e003d15502c0c1210000c00078162500f50500051000e5940041618000c55280095000740240100300400c410741c0035190186000b542159109401d00091045600f0b090b03440c8000d6000b14280300405601c140e9402c584a48098495403d2000a0428078291a600b04001001c0f4020380d44408801c8942d00c604280c582c1704541e0103140524184002e001300c1014006d4a00503030702c0300c001918072040d58000349102d403041050b0980e02e60391000c000303480d43c104802c80f500ca405120040340d00060000e501c44147c6800178940c4c0d01c3c01c2c1c03070540118116407041c52a00a010000700941c4d400d580d003031020340f000714028403c02d544c0d80b12004008101c4c0c1c04c02840c2078207214000c00048007203584141504e0303e11000b81d404e089802d06c5070001583d03d40c28488000e05142c10840c95000b00f10094 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 332716456 1250 332715206 332715247
    0x1209030309050123060d02130203040f1e080a0309051504030e040e01050114010804050a06092103020316200102030a060806010602030415081b0d0507120b0f060717 72
    0xa07002084a00b224540da1005104114031403004c0703a03d00f10205a103490000380c944030b500d1000f414aa211580707064818144e1b00b040f43c00b62209001d0141a400380a10306140c0748451b00100001000b41c660ba0360b420205000d4031034144105030392840c080c0308004042100130880541c030601c80046140621700109000e03000c9192a008034141f1ba208135241c1014081d69060350b45140000407442c10318401103842000092055500c0d1155200040c08100303588180d0082900503444d0450405c6000351808a40181d54103040c1058410010014404215501c13110006400d1a0810401107448461110492000e01c9015607510000901a0a00803a442003084484c00c03401c0d11000d030398a81059031640214820b2170440f0012595440c0c84a01c0307000f0169006130811039848007004400f107102c0c25500141554814a40d4603400d002c00c0e036401502d4215086282d00c8144a03600988011454040914490600450340440c00030f08000101c075000b050809015501d94803542a820b880f41c0030201e8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 332717706 1250 332716456 332716463
    0x1e0608181e10060e1b160305040e10080a15110c01050105040e030901080109020904021207170901050106020a1b090507021605060703080402130b060a0f080c070c06050a1209030309 79
    0x707030481040001c802d401036078101c621626080308180d540c0c4110406204e280351188410000401018043c400d07983e0080080300e01a83c1e5144d10b0303e0610480341c4607110090100265481c91030002c003d19a40002e1107407141d980030070960074009411b540c0c000a0019079071400503420300822022105881540000d0403035400304c81c14484a640311030b00c0d9031a231040c409403d00140f44280144150489038004195034000034000500d000280301000030850401e80788100000c080c0840070316034030010032803545c00001d001c3c0200500d516080c00a9502c2c13100b554020301c08142090740000369800072003148000d01d4005414012858100002500c0d0011660340a8120782c50410100c0c441c1000d04c156000a070341502c0e00d800d162919004c0015401001c0340091500b51507011011090311040c2c040c0010001e140c0300d0084070030b600031000e00309040c000c0010003000710501c040404a20240d24100403540c80382452995451001e4080392520924203012051a00349000c10b000c059141c0c0c046881c0c0b602 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 332718956 1250 332717706 332717713
    0x30905191505010e0f070e06040f0314060106020d11240108120c03070212160608090d05030c1207090803040e041208060d02040b130504060c02071e0608181e 69
    0x400358807140032698280504006840c1e00700008950101d444003464005001d1b0400d50085046440010350586c070036086240c9010100c01c0800801c11b84411a01580910501400c6191b040a00095a400d5800002800c0103150503c410703001d481406683d00c02990318201c1c160801640d4158044901d0a200d0400c09118500050500100000a80b00d9509109015501c0c0c500340382c003003110401d008070409901f801414030b81c5500b01c3d582c940c1040140b0142e29141030610344013080c42e0a080c0b01900006c107016003081040342c501255000c5801000d0144500f03209900c45450440348102c40e6080741c110391000040204030310010b0714006109600c134000100318805140811100c008068540581000581080c800145441e803c0b50516000c003400100000c054100300005592007600c0503209603941d5040490620350510144000c2c002c1c0901d8811150740703001d003050400c4504c0c41008100803034600402d120222290f0480842494641240e050301d03540c041c1c030181c1d100c2c0060113803580d22 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 332720206 1250 332718956 332718983
    0xa02150a110f041e03030f0509130e060411010e010c0b0a020403080c0a1b060806130b030304140a09020f160203030706050f06042d0e070b040e0108070902091c0303090519 75
    0x140c020484d06070fa078150340d1441c40605560040d0751541054200e0703070f03101c842c0340222a0160450b109400d040344e880f41c001c106a05060074001c0240007554101070400011150300d180591b00300328440403643c1d02505105ca44c0c0d640b0340c1640000d000361f400c0104003100005a000200600007400004240510342c1040e01c5010804951100b0610f8481c50700401e015074006442490034016104041240f1140460001c01c500c3c0000c2c00d40d03005400c00d480d107044246070500c041c10507180300405800360080462a000703820440031040d0045005490114507081800c81c1192001e000707842416a00c81c00a03c05800c1042009036904001c413030a40c040d510340503204100c45121700000d00b69070300420b01c4451208190b00b210029203010380e0203078000c7c410028005213002d2520300800080c25840c4419401d541070880781810000705510000c030190040c011040980d6440c1800c0d6800040c032800d611510200c0c1c0350640c01b5080a082c040c21601507081c0c610240701d001d602d101c659509c5042e8055940 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 332721456 1250 332720206 332720249
    0x2070f03110106031112070911040807080303010e04120504082e06051005090a0e0a0501031403070201440105120619090f0b0c0d110a02150a110f04 65
    0x200c020748400342454000c0c85ca0952542081c0d04580c0d5450144415a000b05413200c002d20305a8180d4007000006c040d0004040220b850b00f406904007412442c1c001d546194584250107100880103080901070305044018468554020b17000c4030010000c071001d480410f45c0488002d41c40a030b000c80d450070980641840c0c0e6030001c04501c0750a05861004141e540041008002201c80740c1100d111b1581154046da0045a500214454984501c02e11000850923605600d0801003245501101403120340c8240185030040c0e07044041d6450000b0511461000d069440d500c0f40d4010703e620a440f45028112030504812881400340c1c035060ba101583d0140608400318407103070380c90344110388400005000d550b011455401d140c2141c0185401607a801d135000c609500e0705026140f0650354042d42e860001265840081e05020f0100f1240b00d2000850900b804490081e49500b01d09110034460016500010f026034080d51080d915685404050b94444180c2d001018180c1c0c841e00460158030300030000082c0740c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 332722706 1250 332721456 332721461
    0x19030c091509140301060315090c242a03030e01110f07080a0203041715010e04080703030f0204080307060b04151d1504050f1608271002070f031101 65
    0x3158625a0740200c2d440c81e00d20140800740380100c50f02e41c95521044000086031164004a04407102060002001c0c21940740132107012043d5801403961801401c480306174501c0000e0340000641960401c03540070b0002d6486d107640b09032541c1c0d002110380c1c658201c0b02c007030552551005403000c049000800620442904060013402541c9644440700e05c200222340019003408003412054a1500480c0e0a203619400c1ca504040d0724011801c0c0640c1c031454002e446031104c494120b004080c101c092150300d042c640c9a00720180300d00d2078090281502d800b010038141c03603e60b040310020080042941d4a860191030400c029042401c0310b544035a0074094100030a202d801c08610440e452904ea4101d46240000c3d1070498680051101c0001c1c05603074415081d81c0c440e030007407a00c1001c0340030a5003000e18000e600c00d203603120320b511410304001d000745c100114081c44c80354103004120300302010008252109182031400e0200000c15542030b0000ca40d4104101d03d0b0004900340c0e5100341c0f200f54071511400030300340c00c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 332723956 1250 332722706 332722739
    0xa0c09050a030204090507090617071d070c0212071206050c0405030a0210031e0f0e1506191d090d050c03090f04020706060f06030b010e030c1519030c09 67
    0x184212a00e070104018031340b40e4880c0c1e6410f03101e00155000136940d0368264007261840e0b480044240007a07000007685160901200024054a16944203140d640c0505641c40c410b00800a40900c101101c2c1c4005641d198407005500210b403c044855064850700c4170001020f0340582100c0050a01004c00d8803900300406440c25500702500400d00150a40c081000034044041c060f414541d40c4d0403e005542d50b030a07420340040840c4c0740b01140030044808114100d0f501c4010080c0345401403004d0300d90615480304a80e40105045412007926003d85104018941981d0f00840d9030424054884c4100c2202500342803050800310203a4610b09003d007420b580074400c1075402c00d105d03001044080c40a10741002800e140c040b01038801400d001c000e94500040f1071161f08184041150b901c0d040161aa050188901d21002032900003a00041d82c404281c4e61550044024400c40c101140d03015515503440c10f440f91107a003400110358902440e80060b00600c0160310100c00a07180440120301c40707421120141 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 332725206 1250 332723956 332723959
    0x121213080c030a020d03140301060c0308060f0901030b100b0705061806040b0103170d1826070602280908071205060601081b04030506061e01050d0209030a02040e060a0c0905 76
    0x500e02d03c1942080040d044a0604a040c450401e001031440c410b85405136000e007041351917184046003d41005429a03200900840c0319011500000aa548035080314604503544110400001d0b15032440440c08042980c116102e003240205980c41030000000e00d09026440c0e43d180d000001040103078160306c5800480d0301a000918034401000002d000000d07000312520003d003200c0c10080f19030303903001c02d643e0f00d00a01c2c045883c4030440340d4240b181003200341c11040e142c0c00c011104003007000006521030040700009019198085480c440903504d041ca0ba014030034082612030700c0c1800204000e811607006029002d8a4440c00c01d0118a0400c103200c1d07803c119400c04020080f0f507036a0001106e1407440201100c00c4a00090b0040c0c0c10b03104400064000b035071042c00a8445403030300400b40081c4a13035200150130180c01c1c0b4011444240d07000b004507500c0030408140583e41c0e001c07903000b00380750110300031000390440d180500f24100c1e02c20205000c0d000300300054082c00140d041a508490409060164a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 332726456 1250 332725206 332725213
    0x40b04021911070e0a0509010b09010609051c021c0b011d01030f050a05120913060b0a051303080703111506100507030c0b150a080a0f060b121213080c03 67
    0x2005514000c0004203080c51204080f10407481e220350410351034180039038200d00c10a44400500011010a01607590480760a070392445442d803400d0300c0140ad081081c0300780341c014404100644c1c54000d0540003140b6407078010340855140c9040043c1408651003900040d81d010ba1f60780d001140701510800700c0200304066500842599080d9110800b0f0740000c4d9004550364840c4442c4c010000d6414001c403066641000d18050300d030301c00c0b031043c80000c5420301580c00100b0b1a00b5406e0001e0142c4030b0940705400068a0300d80e80340c00900716011100c40c6103400c0648458804502e0b0300425501880c00c403080c05034401a50350360b4140580c800740301d07641940d03419400007404014034000ca21810140c20b807107000f0314104000d000d8949038040c24650031384414030141d03d4400310000f1410215107580040c490040100441840c0391100021151044c0006001644480300980141c1e0b850703182c00c4c00041d40e441034407604200203540303010341c0e0b1000d005284014030140b4001141c20005c610380070340d030324050040c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 332727706 1250 332726456 332726497
    0xa0201060b0c1c03060e010324051005030c09060619051309021e1e03090a0804030506070e06040803030109020901030f0c03151401080604091a07170109050123060c0a0b0105040b0402 80
    0x40d1003010711409c807209864070650b075002410075020701070640118510304910318054100401c1c5400c1070501c200580c011b1001800b880708035101c03001181c6201c5c4079142d554078200c884071070896052103109070740c900202d585540418104c445900419000d503c7d501c0251440700d04070b0240041c0d00550b000820342c1c070582d81c3c8141d28925950001c0d40d00c42d800000741d41c010786483d50350000d183c00580041c0c55a6008600300400c158003e040079250b8203040341d0840c1010314240010386c0d680300500032445101d80208040d1201d074082d81110b210424180b00901c05100760220040c010302c088031254030290600e540002d034402c42d6a40d103034070400060351010f00d9a514082800050010440100c8a12801c0030020701000c01142c15a4040c4030143d4a942d05c2c0d9900744004150041d040e0014460345240c100104000020006001080756076031101f51103002e80c400028402d8016070540203414098040304100f00b0a00307265460584404503020000d0003c000e06100c100d000d800703008100038510800 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 332728956 1250 332727706 332727713
    0x1150201050105121c18080307060b0619030b01020c04050a15140114090d0519050f060f071b150b04150b0318100911040e01090b0601050a0201060b0c1c03060e0103 72
    0x111a01c810450070106c40c40340e0340c104c0d65817001516900c104229080817600d074082140318060307104080d41c1215440d040800540d045040c00d000c3c2e13513410f0b0a0541d50085000b459000b03004909007008010810401480e00e40301359009004c0300c80100110764900b0002140040c0d064006880c01d80040e940c100c000002c91130909403e0f0321202c12030383d00a21a500510016000701306210000f50609054003002d1400d15084d40740401ca0035006106030454010040b01e0116200380c2603202001c2e2401052110b44244910003110510030003034031004100c5162449003d280e08201180b80d416030301042800e0258402c490010850300681642040801c0030910715101504110020400c15068940780b900702c24001d81161290881242c04003218407440b55149098031807040d02c142004020311007480e43d070341c8481d044480140f04034107101001c20b0701c84503140b013503110794080c04100b5000d0b50358004400c2465a42c0403050801d0700905c1620783c00340d0006200c1c1c001c3e50120344040c454090302d03908554 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 332730206 1250 332728956 332728993
    0x2101060b03240102060c0a0e010306211b080606060702040b1809070f0806060d15090308010608010518060910080105010305070306051008030f16051605030606011110090311060115020105010512 85
    0x1c1c808c604041d29004045403400407407034040824580d2018000d00700d0106d282100340422949020204000c060108002e0b80402055050340010100c40c0240d4a0708148001002081c80017000c42e0000d00f2440640c903005d00c01640700d4043c00112084810322035407000c1107805c0c03c41070700810200b9001800803030018144006119645c40c0314a9202d051007000c0388940c0c003200c03025172080c3c0c0010081401004160b810413259400b600c0d0580f00b110f042c4160003491712a400010341030500580c00c1c040090b01d10038032480c40c0c001400d0450001d0141c0d5030f507402c255640e030702c850100f542c10300d01d4000400c0d007042c0105400402c84d0045000b9606120703102301107216903084402848280320740804a900003580030f000d04071300d0180f054004810a41050145031410b4401842d035418814541160700c2080c500003401c2041c0304d49554040b60403020351600300c803001d03944822443c407403185000103d0b460007000d0340c5410085042d030082240c0c1e039030388080105207000e901400107a85c100124049410301ea03503 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 332731456 1250 332730206 332730227
    0x140105040918210810240306080d0c1101090e0c0307140301170d0806010c14010603060219020c091e0a0e030a030e0c0607022101060b03240102060c0a 66
    0x40b101024100b454840050110010441401c10007003c100d545485402601c1150403408842e180394419041c4203c07015807400034030040d02c1080d00c590984074103921039000403004d010751400792001101d40c18000b4041d00c01c0c1081c101d50b100111021700895511a9000c00700b21100703000068204c1e01c4603c80d03183c1c944e202403e070341c3c02c0009040c1950240501003000754000d120040c00410180c400c0c1034450b040c228042c001108002ea1a420b004642c0c2e03000350b10340003190700403007a19481d5100c03452413401001507903c01090140041446407080206010601c01207280c2d80a1315030310309201007040341c1c0c164101c400300c103840c54400c2c21180501890010540c132200741000040c1d0032010780e041525681001e110040060740703450343c00001c04002c0c81024081030341035078010705224065001440c5206c04502c0002c090010450b507090130042504114000c00c0c03c480c00301d5030f80c14420201c3c44000c031800740c2042a50055658041075510000c0c4180c481e198100909041a008031000c41c0c142d00e14 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 332732706 1250 332731456 332731481
    0xc1212070302012901080702010e101a0405101706060a14030109050f03040f080c1f09120305030a050708040f0308060a0e01080a051c0203120a090f05010c0305011401050409 76
    0x200e500002c4c00c055404054505002d118a2009014080c00001065070b5001440708003164104400d0416109001820b2a4086011072020034420907480303a03420b4590200091503070103070401c0148140422200000000d6605213840600350179000c9072003075074039901540d01a80120244400704091104201008950030000340007154810141d03c40e5071034021140681d69140c0c2000804201c41150881140020110800909081d0544d0030000300c0703121001803180c1800031452402c50400340700d1442d81014100010300030198544504005085410498000190320703e0500032902d10340c000da00c44c0d442154015400f0103502c00759a021a40d0803c05001c070b64018a45400c0450b000b06980c91050280442000405c0340b408170741000c51400b07523404002601d504200301d1a4070140d6000c401c4604044ca002c445100350b0b01c41d112080c00a00e03403814041e10b60800342608104005040d0000030010040b5a01440180d0f04c500f00b00001e503000b4259a800f20340104000c000301c0096401803051001c8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 332733812 1106 332732706 332732711
    0x18020d0c1806080c1c0b0907030204060603050c0304151d0609010f09050703062a0201020903010b06040f03020d0807020306100e010e10030308130210110c121207030201 74
    0x8000813542c1c010064030646450f541c0417408107005065101200201e64540402500c0c2c031003126000891141c0c0c103000001681920901070b040c041c0742104111403440d00ca50381c030002ca142d0030096908000381c96004145000401a400b0094440004017900c0d00b1715002da18642104c507102444c0003280d00d0030303180c1030210701300080001c00da075480000090404014500e541c0b0004520b1550701d860200113011040f440e6064000c2c011001c01a0024000340d039914040110500a500521b0b0301c11311255010000b500e08810510346d42800f0b6040c4034070b0b1071003903004203040c254101c0d000d10f240c4410724010404080e148200c0c5004010500c41c0d01e8160601e400c10402c164107a1201800700301206000c40e1340c00014405030a02554000c2c035081060300060400382c10403059101c400c0c928000e414852840d800c0007070b0007495049001015040210114039518111341020505600319035 = true := by decide +kernel

theorem cover : BRFrame.Cov 332553956 332733812 := by
  have h0 := BRFrame.cov_init 332553956
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332553956 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 332553956 ≤ n) (h2 : n < 332733812) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
