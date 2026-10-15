-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4683
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:24:25.679042+00:00
-- url     : https://prove2.me/submissions/1fab3fa2-dcfb-40c6-8bc7-862d05119ea7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 842086330 ≤ n < 842266187 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 842087580 1250 842086330 842086337
    0x905030301030f15090c0902070206120103050d110114070c26030105210c09091623120703031b02090c030109050c1204120c05030307180909020d021908030309100c 72
    0x5d40000704001a400304242c0d06030010240c1d8450704c07400090304501035a4000c08422901d5030000040003c00100241070040c036403039100b40010100365a501701d840c16040f441c0741281102c0081c0100f0702c40c490600200c0d108684c20640e4035810307502c1e045441c84141081124800000051182c2d280040b11481c070610280700c403929094a9482440d12045480855070142161802041ca072800c20b20840005400c5124003140340d40e035900314400c200c060b4510211400e071001c045100c06050018003841c039a035810b0001c2104a1442e5412500e071843c408807801e46414079001c901c010703954090710601442d54498569120350511440100b254400b0781070308030b18503003049500a82c07064142c003d80c2c0039402c006020315203095400150340f003450092008109000c000700300004d0350340055203c041c0280000340c4135003e13a1908800c5088410261002e580700c0007280d503010041c82c0c8003404102291503c81c0c800d03003060381c0c0d8203028038603003040d545954140c000d48000f182c1e141c00392250b2240080c00b4038 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 842088830 1250 842087580 842087591
    0x204030618060b15071b170309130c080628090f050a0c09170a0f12080105090106210204091e0506041b030c14030117061f15030905030301030f15 64
    0x500441c9a00c1007040051017400403680d8450a8410790091b18003d120308103020401c50742991429459600400d1528840c1c26400200100180d07188540590082961510207441d202c040030800c0c4048039000b10000034001c08103140403003c3e044201d200030247c40e28081005929100c6401c00d4820040c0482062803400f42d000e207160360711031115001c98005e04148010740c1040b0038400d041c6642107101412401c00d052445007000116284000c1c001403940d2400216601c607410000d1240c1c0c20b10130240040d068800e5000b9000c0d80d00444c1075000044180149031581e980404c100f80e50030010968001141017204a0000846000c0c503544404211001c02103d40d162a01d225510540d0002030708250707580101c0090741c1d029510400c0c081d15003066658a0750794407030070199440c0000e241000c0c0c0c2e018400203d11210b4081c00f03020304c55056504003c05150610070b10b2081c3d007003035101c041d003007545a40041001c03480c1400194003850044824030304090380e5007003040e1082e40380c03498117020f545040c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 842090080 1250 842088830 842088859
    0xc0b090703021531050114040308030103150f06080d05090f270f0903070602070609021f02070503060411040902150c010501050a080309032a1c1b030c15030204030618060b 75
    0xc900c07040550300301f4203080b40000760000044d0700c07a008640004044100010011007404202012042c42400205060008603d44580c12040e80e80610a440c52030340a4440701200c00d001e036010f44071400c8041c4c0b10032302409000c80028480740391005800021150801c120440c0318841d038007a6800840b05284903070508003180035642e00c4c810500060406503021a49804110007a0040f0074042d40040042140768000000810004528900074015119031750700012203003000305620707119540100c0c3c01e441000a110903c00a4001d40c0d4040340e208001d440140b0100098030082e0003c0ba24801c00025a0742c113180c02d01c4160181d5400c2507809604c1071110b1400341d600001d285016482c64400b000c1c852018981c07803c5144010900d8590141a880c410390910030030380043c9039090b001d0039109844501500b203010708100d02e400080c1031070788041d40600c81c2c0e5100703030a103029506051800610342507490310703082e0032612101032420448040041c0c0d0070a01c0140e0042800c0e28200b02c60090518084 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 842091330 1250 842090080 842090167
    0xc1516080f0f04110d030e0a14180604091403041509050619030b060f091003050108060f0c071505070f03050108100e0c03010c050406090e070c0b0907030215 69
    0x1400201100140b0000800700244913111000c2400058018004242d2034600030b011910741003051405030000728400518580d0a50942e021900701401864600074250309081c0310300801008240c01c00e440f55090f80010340c8102c0c1d03007012004807101440d00d56084c4040d0804d604080c0c0c02c58400c1028602082c01130765202030448005400e101325182c020002c8800c240d018161200c0155400035000c10010446850000181f03143d0b40b040b83c508140c1102118143e003290428001e0009503808800090500c4207a4042a40c02440d0721600c00e06018a941c0c2d030602a41e010740000c814240c0781c070705009226800c68503400040c0a142024442581800405652140c03001c0400080769200c04070515610010f0000f5640300030302600034802031001c010050169405441240e000524000000405401c05c40f0700c41e000e0182a62180345a80103030315080904d200c02750400500340202003000005a841000c03440c101c040c420034841c2ca9004410314520300c0911800e843c0c091807120350a14007400b24 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 842092580 1250 842091330 842091361
    0x1c02030103021c02010908030a0908070e011d09100609020c010b09040b1b1c05060a09090b04022205040b06120a0c0b070f0c0e240102100b04020c151608 67
    0x100c1290b4003c0c00f229400122000b080587c443e8801c2c0c000000c401c041d00d98407000c1c11003918441d508031074410307981d80c00220382c1103400d2094107090110540c514180c004144281500642c4060448104000c0c690100e4211030fa40d82c0310301d04441e80042c6580c50401e0a018011680d80e04951024103890301d9100c2801c080c600400ea0701314032201e48015209280444140c03a0724030300b1441030f00d0f41c82c1ca01d2005c00700108030a58800340f240c50742040000d0703e0001c5000b59070109034080f010000d151116802c0c840380c41c4010008140c010b00650800f401310025105592140c2e02501040d2440e04190313040c05803403180304001d84056080b003e43c840c04161092042412100d65024041e62524035080030150745015010050403034481c02c10000e041d00700303020100d0160600c8824108024000c01780345800080300704015004d60060400662011600d9005d501c030014044c1000d817030f00910122003810000344001840c0c042d108202031000c441386c3c2d0b0711001c101c80e54604001669041081413007a9105 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 842093830 1250 842092580 842092609
    0x38210903130e0603150907030317010b07060b150a0c0b070e0303030103111801090903090603052707090c0507060614030a1209120f1b0609050d08090d03051c0203010302 74
    0x4820402141c3c0949040048600780081c0030b0400d41d00741403107440c5a880d00501c0c4400c0d00058048a80074a1120a900c00b160403907010607800c42c503012460340e030b070740240a0707407000c090340000c04017154048007042c08000d040c0c03055903540319041d0b40b145290a45154201500f0b0b10100b080c00e041850060b00c0020449054a80015054200716448000140030621044034112100702480001540450b01d0700b0095910b88242c98070301149440d10301c22000c66800b214001940031081c0111500301c059204000000c2101c0d0044c0c0368000d499400c82c40c251010516000002400001c001090014511500014141011000c014036001c0f00009548400011010348109e2840c4103440600b406050b4081c014010001440b4040b82c0a080603005c00380320740d4040c1e59454a10342c00f030260118403854242503413075a40390408220b0508040c0f1001081810044072100e4041000080f15540c901c401d0408a11a40d0b07800d580f0f26040294284218840d04000c0b189401440180f0041c1d441c242ca02d04d404 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 842095080 1250 842093830 842093849
    0x160b04050c041506080112020105071e02090115141305060a0302190c110103150b0a11010216050d03060602030315062b0608073821090313 61
    0x549803030400508010551034240d07031240c074200019144a0502103100100d522039118020a80c1ea01c07051803413213a400c400020b001440400400001680706000b0b50b00c00f8407040d52002e90000c0950200726021004c0c0c02048084403503a014036440c0b940b101c45407000c41440d001b018180b8015031102d02003281140520351040e4000f06aa40d4410300c01d506a035604d443c000d00034085092500c602806149802009a802ca8440c54110395194041c1c0a00400b007900804101c48241c40c2180e00d03200ca81110b2203540420080305070b500c600d1042400607003541d0030204440ca1900d44281340c440e107030080c038110395010b03d41820740c1000b9082c1c0202c19290302c08a014404200b0000040005820744548514400b80140000c499003da01c00307544400d040790742c4e00504100040c1c407440c0c0140e45a03041e209041d0300d40b55501840a83e03540604190740407242158580d01101036071140103041e50441c0f80340741014017840c62850f8500b0441c1d80c00700e402a200d14003851802e608000e100800314100d00491080 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 842096330 1250 842095080 842095103
    0x30c130506011110020703140319020a120f05060a1a030c09010e040c03050105011805030c0f180c190f0e0f0126090d030b011704060b062206030216 65
    0x82e9000e880c0714040150b1a406480c020911444500000e4020290a50008581c0e020700d4580440d441c0071213000311522890102070760409620b0402a6028080701010040e0f10b2418058049003405400e08804003640b000c01c01b450504140aa22940d40d840010840a8610440342403503800c0d003204d0704820010580c594a0040c2001604c26000d0f190300550005d140100812020358141d02490507140700341e1740c40c0303080601540000d600300b58034041c0c69410341000c81030511924003141810300d40f160240c00b01e4030300c50300d080e085070b0301c0007085528045c8030000089034181000c2000c181496415542040d00020840ca43c005181c0070300d0800142c0141d00304280080103a0042c06140703c4115464403400d900007802d9000c120340001034030500c03518440c081280140300d0082c01810303903010301a541e218000a607131140034000b050140080d500a55900380200780b50321003070000c248214113880701101d444c0c248050404815141d500010405106000e481c44081214407020410364000c0d030310181 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 842097580 1250 842096330 842096341
    0x6100603091b08030d0501050f03032a011811010503010e010608040f081306140c030f13210519080409090311100b120106060c0f05101118030c1305 65
    0x8000901c440c62042c41106140d00140b81c0500000400c00c0e07182c1c0e910140040d982c0d170014003d0b0501b0a295140d8103820038001d200d00040104060402254142c100c02c640c2d618a01049085940995681c2e08148070f4031400300902c480b0880c3c1c204480703420310b401c03482c66140101c0641e1190042c0281c2c0c00300525140420180070b910100b00d4903464115a105070341c0d0815035662903040505109000c0850040e56480c101205640c0c00d440e00c03540036101071850081c003424003207040d9104003111003e0101021012a000c903008130700b46655561985460780300c44140c00e00d2454031200c00c1c6904000c100d91041000000c104100341d6048460a000114000b202c2d40390680f01a2003000d0300b141c40b446041004e1151100980200d003442d6025a102035210101180385401d0394217a02400d80031900300b80500b400607000c104840703c0180070360259065007400554070310645061144440b910742c00031030b00c411000e0781c140000749190b0044004280d08030340d0002052000f161038908480e129501c0c00003c1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 842098830 1250 842097580 842097593
    0x1e0403020a0605100f05040624090b03010803030708010902070f02010503090708010e0a022d13090206031f05450c03040b0a060b1c0b0a030c15020610060309 69
    0x2081d480d4080000d00107454204144928603a03544908031842c1044900018a41400d219030300c1070f24500600081022040300c0c022850400307801440e0b0820210040c00584641c142024601070301c020000745580c0d040c000802000484103820881e01c180c1304020000016500f0010000ca030b660a00700661259204140725040c495154441d145a500300600891418004285130364810320840f0044464040f00c1705540030000b2145d076400140d1051403405080c1e1624040382d002c0c80892450100380b600c5d4a9000c102950400e48449030290089140c0e5080300001c8400e02024040aa42c480300c1d1414481030f01840364980303815003620302c1000d030b400354004042da0455901c0410300804c0c610340341030041c004040d641c01110140e40c02c1d0604000704412003040d0244408a40401c0d80450500d840d0740b101504030300d50440403100a0750398621301041c1e03840344405500214010350700b0100c1181382085041d80761140c240540e0840d040300003040611402005c28006942c03113072500141e010386038507212 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 842100080 1250 842098830 842098843
    0x2060a06060507020d170f0d110c1506061306050c0f010c120203090f1c030501050103090803062701150315031e06060909060204151e180b1801171e040302 68
    0x50006c65000215207038018200d01c002c2c40b00c0d0381e4850007001100c03546c04000b0414065103000940c81c0d080f0b0441202055121140c0c0382e002503005003201e00e0110080d80d462807400269200700041100800e001e420003101707020814424a0540c000e0080c0d50005400800b60341c455480d048500b640800400d0512030b0400c1048203181d6404221500880b11010314019112044c0103080028200700c000300d4a540b280c040c4400701540034a2035401d40d02d81e4800c00030b00181c0c982c0e01205d041030b0041d003030310541c92030b28119000f000407512140c0b05451340c440c01402e803414030b00c05211400c0541410800100792038180800c407071029280041c01c0e145450200c01401003544805ca0345400e20b85a001840425030050040369040d51388000044c1c281038050f1601101c148804501e0078003114420401030240090080c0c031071600b6240207042e616035100c400c440d00026152a070713560f0f0018035000c0e03a5821210130000180310100d50782c668078140e035001d0b84004c0c00c0685941122280000300e000c250080145 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 842101330 1250 842100080 842100113
    0x3130f0602030a0531020105070f12120c03020f040302010c0512031509060f0d1b0b1b0d0813030c031716030b010c030210050702030f0f03010602060a06060507020d 72
    0x55580e0300f001064240585400e03550701480256081400403065580e0101224150005a11207006060381d00103440c1c0e90000b1030166030700204180c65900186003a07942105102a0b03455410507011812180c074200c4138090305982c06c1c544100004d000129421083c0c0b4116982468500000c0302c10b490071a061150040c10480b00c0d07030b00402448505409110b00104401090300c0304800c035034820b020802005e038001ea0458004421001e2100070445d4654000a440407207100054400e54901c200d02490744501d00850000a8540410804260920842c00e03d568103281403081400c01c10000750b000208100c0041c00d01024030035020405000b502100032195200024011601c1d008103400c0c07000480524100009207000018440342d17000340c0d010510960103a0040c01c0a000c071886000c010b140c0540320b802980f000f13208103241c0e85080c0005080c1c16400b42052616945010720103440c0580c041d2840c844981458000d0212913880350540300b8103030b011110006c51031410709006003205115104c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 842102580 1250 842101330 842101343
    0xe1e1204090207030e04060b0a0c08090a0e040b0a0c0206070f230d1103070507081605060705180a1212030608100b010e061e0c25060e010f020303130f 66
    0xc000618014035800303031848600988418145154000410040703443e01d004040003040144103c1e0070b01c034407038000c28030103a02c140c40c45883e040c0301c3c000281c42240c6c6988201c403110303081800c000400140c004407a4204817201c505002c11090004080c0d0bd8403c02080042006485c40d04032110512800014110f103012080020800c02101509111540b00c08800c59401e81800000c0c00c26000078400c503441002950f981501302445641c45a115501c01000a40c80300c0203e031009001c03442c10301c94540901c0c12510391a0742d9031130001242c0031900d03040200520441d007404041080000070005440c84690118000b40c4200002c0800e13002001c260300407100c2c038416a1185200200560700c5000003480036250390080103101000c1090521803141c20804105030101d07480c417101480c42c0601407550400058038404000007941714603513000c484a017002070100080403c8043d41150940318600001e1801c0002070110310b002035528800900500c03110320354460042c090280c0c80325404c024603444131 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 842103830 1250 842102580 842102587
    0x80c070c03172107020c1002030405090f04170715050403110a050303190207021e011407050102040518090a1b050a090f1803020a0b04020609060a020106180e1e12 71
    0x1c00c1c82d607054001100d00d120324043c001100100b459070ba100140b04540b558000c1104100390010312191490031803140080d8403041c0004166a41c1da000068481d1486e805103031540d29140c10400c0090030214002d1001100802c0881c0100d03031580e419401030a18400e0204450711179141c101c40300c44090301145102d0040002d00740070001c000c0002c500a524140140c2103954034460300074101d1140304e03802035001810741c14a51826110003540d1000810504081c0c948040519a400c41c40d40122400c480c56580042c0c00c0c46107103040e80460380400b101009200c003510b0000703c1c0a076200000000944810380842045101e410300c42d022001034a0054801e9481556403209800500400601200514144000e94481a5002d801c2e035240c1034156000f0030844116131240c0070040400b40c030580e0454400c0000031026140d5100401041080362b000080192900c1c3c440d032109401041441201420f08015420702c010005046201031416110f001c8800000070625203044483e560700b00c00c946010 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 842105080 1250 842103830 842103863
    0x110306190b040b01020618010212010312081b1b01020c0d09170a03170c07021f0e150d11090306131407060503160e0307080106051f080c070c03 63
    0x103000c114044641080c0c140240020001080700b503c240420260060f4130800004070300044000c15403845104070070005103010030074101189a10000d810503200c0102504000140d26803001d911944052604034030a001031500c03600448510a4210504000d8200190a00f031388200794102c60842c46c0540403128188150807001e4011590b601c00c0c4401029070031110f0390040404101030803a5030345561541890140e038000c0d69035140000c1c02c072140c0362500b803086c603005032510304030961b50050000c94210041d030303000c1000701014668040c0c5800f0f6110760f5100002c80c14003106a03080b20300300e4400410005c00d00c2420380c0c2640a8094660741c5880341e44184231415800c6c800080000f401103250b1103810414042e442d0b81c80040d4401c00d0005a0100b0000300c4078000c0e005000e1110a891070200b030400760030400646091040d41013a0035a9554003010002d0789083c03801c00101c480f0b040402c8400103400d80c0040e25104005003c0070900d040010100204584607480001441d80400d4920450001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 842106330 1250 842105080 842105101
    0x9020d060e10090e0f0c06032a040312020a170d0b1305160c020609040b120a03080601200303010302060304020d06020c01050f0618011a0408030409050603010b09090705010507110306 80
    0x4503c6885106464040103244108000c80e80d00c250982000c018110782802c00c05010b440e81c802410740310703150002560540e40929118160361304603038102c441521141141422005c1d004000328200665015050790b00009111031001501c4440009105440b01100311902024103484e000059001080a08080c40c2c00b0300c950120f030040450740343c007180082503c5001c0d80d200740c1c4040081d512040134000540d03145042d42280000c058090911f01c00700e04080e001c140360580f010b40450100e04244100b101d2568850083e98101b04031402c8000c01454408d403807610f0303210602010b070041c0400000501591a0351100800ca04e41c42582195580f15000015000700004d49440b080e03101c0307040209600c3c0c5090080b904403442c188000c1c100343c2c0d291403a803a0b80720142040600c0c07481010300c00003030307640800d2014000405200d5404600c6140a004044c212101211540e00c01c091a030305010000500103031041c184d4000382422503523100076041a40c40461003100032541841400d0802c00c05020 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 842107580 1250 842106330 842106361
    0xd050a03020c10171905040605060f03160306020a050f0a020604050714030c0d060e010204060c020a052e140a0c02040e0f0a0b1e13120302030c0409020d060e 69
    0x1950aa84007204040d0400403500c00c114012030015040000039000b024503242c903941c00c10f507078960105d4108000b01c00315055620880d015200c03265104200403250509089280c4d004400314007a000f001d05150302558806d11a00000d0f265950100d42c80966074001c900300c0d0080d025641c0d40b2501d802c44640029544d04007203600301e519014084000a400d030315030a00d00401134006000d07010f0200544c050090650b500d41094501503240c85035030304104001e10003070008c8c00056a900105a80e6801844140210741c0d10240c00f5041860504003c14001040c00e504d40ca0844051000c207144040102c0e8070400f46040c3e034284000000c3c3c0080415009402e102d5001d04c26034080c0403201040708641c0e02d0303510240364854250070400d43c000009401d51190b6900c48403c031440c018907601c9102c00c0391601400c030741e004042008240803006001596407003004e160780320b01d01549540f61400002042c1d028910442d00d441d0b0b0007240ca011201410f80000c8040c03c1185c0602c0707410f1428a082501420 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 842108830 1250 842107580 842107583
    0x181a01060905030a11060c3f09030d11031c0204092f071b0603020301030b0f01030c14040e150618060306070819020a050706060603050f190b0d050a 65
    0x207000120010b2a03003400716010200fa0340100001071207449132020300083d42d109110011560260f0400580c042d400135003800204110709082003090b842c0f040c40e105280807008522104003400707000851195400103850011041d00340740c80c81c44083c4415080c1d20b540560b0314081c030146246040400740c030060390f000c1e0044424001c820b000401e45444448520200d880c50707003030040c1160b000140c00e18105c000800e1045e00c118403041c6250035503d43c06a4560964220030002600000100284123a5400b099041280ba5000714865451940e81314061082441a00c00314610b9591341c14450780c56512141200d00c104017950150219886500d00b0180c04480403071040720b100c1c070001c00302d4003640542c030720405018000b40042c0d1140303141070317031074800050a1140581107042c1c1c0b4400408540054500c4817010348900b6181c282d1403428001b5203013950040c03400c051504081142810084103900c1e00064208141c601014000340c400000c1d20b036104980b83c100c203507011322004005000400c01405da = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 842110080 1250 842108830 842108837
    0x1815170c010f0c1a101a090901331101090507030209090a11060c1603030306030606050d03050702040504060b03120d0c05030906070516120c0c0b030118181a0106 71
    0x42c100c00060301c4040205202402e16950315120101c0314500e00c100b56003000142044000700c507900c4008000b46203c001481c13041a401040071a054100702c0c3c450b5005d000c48203060341500c403c484025150300302c0d2040804c4112281c9440170310035402003800350040404030700288603a0350503082c4a035588145100807406818400c001a00803400130490880c4e180c0e02135135102e5480c9800c410494103800407882100c5e1402a205440441418500d6990045103e40c03000316070343d850b600340541182e2081e44124061103100340002c0020b542b00088441496044070009001c0d295810460010710403080d40e03d415201d050307401e03040e84182d88054191304071100014020340d0080700049505000c20b642c8c84505034031075004185c4c40c0d8058005841c50826026403280203816545840c1900c2e0304100c510303c0486d054030709100500520b080b131280039101d021a000c1c0303594581000045034041078861900744a07620f0342c090180b09c240c40d059041460300107a40610010ac00c0205910342c44081c8100e1002c0b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 842111330 1250 842110080 842110097
    0x130504050a03120b010507140c031621030e01080a0e03031305060a0b0d030c080d02040603090614161b0507060e033703020c0406091a03071815170c01 66
    0x2d40c0c41901821004034011ba44546c00d250a40da1809140003207444c000030b09028034850703150940c608102500000c2c00d00b48842e00d2031761410059440f8041003407100320740380f0600c80041d000300c1d4108861588416081c03030b2603017060f038604029074010840b4070781c1c0c21814080002031007402c241400c10141440d014030103a0724181c07100034240e4203d541280343c90340c0060500d140d00b004240503000d10030000340134607210380c640086051950100c3c1c0c041c0d000180480d503607494100500c0094429034024168001c2240d138582480d1090003890261483c0f4001005082080072030003051a011640c0069030040888400f607494500140c0550010041c05000c0d1040d6010103199082e00300880f03407a00e40c00c801210950b049c40302000b0b0301e01011203068056120b80541b81d48207489903c5200000d1003101d03000658800d0503200507040005418250744a5802440140924681e084415010a09414000817084000c00701020140b035503030f200041d492051144014540d8000c11482030401d0241c0c1d81040303 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 842112580 1250 842111330 842111357
    0x30c030706181706010e071b0b011401030e071a0c07120201030b030a11040213051e01091409010504020d09020a091b0c0503070b042a15020109150506130504050a03 72
    0x20501d0010040f005640301500400800d02000846900900e6500e0300e410071403810300e144c8141c5a0300810803110701c1945001000015569041c80c02c280381c091034240b09800c1880e00c3d00741d0750306030383c0592151050881c500c1c040b01c092601c00c03100301040c1d50060303c0310b0310750f00e1a0311460700090340c205902283c106520310529180c04116040300395404218915548841c0003408025040028080c0900000001c0401c4941ea20341d42e014428407000141003600c180352000400c1003005030700003000a01c000b000300340070707aa420a00b213041d17078805e4500503120708900d076403000681070500d40a500300c003010502045c0d0708140e4000c480c000030945000500c403401e1400031912143d1415002e0055081030019030005490780102540041c05003a840f00003514101d9000c91400c520080f42031203a80c1d1090030800d140e004959100d100b4101d0000f0090008039460b4400001409510b4080340d40d5244005030b8035580340c3c00680e0b030483e4040c0c0104034600d01850a242c2d12210190f05502240d48003200c10b0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 842113830 1250 842112580 842112599
    0x1805190603080d15090f0b12010218150d02030106020f2802041e020c0a05100507021519020f0c0606040c0509040f1415100207030203060c0306030c03070618 69
    0x2102d50040400c1d1a150310303000740304000c0c8466000381000580c0342100242030300c403602440c462004500d4000402200840403c41c10f0840f11105401030f900502811204a0178400088117041007698000945108194a40d005206440001002610100010420a03800102c40100c602c0c0712048441d0000c0c00b03860010191080d21004c1c0c3c0c1c01c40303000c5140005083c0303600014003014215040400c0c0c2203050180d0030613600b082e0702c003041d04d0740b0001a12040c00b800b04156030038201010b40400085c108004025100c001128121014503000e90101d030018540d80d030304200c2c0600648086480c0d1005c220300b400e15a01122440b10144070302c0f004106a85017610030703089802042e40301c940c503214280040c0805441101261004142d83c0c500043c3c2407981e122700ca40c459000ca92001c00441c0303a03d02004180c40200d002c5d00110360000c102800140c4000440a41080740e180a841e1030f0b640365000645030800b0450040d030580a0303008005000d5030030412070440401003040103441c40c4e0302d4203841c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 842115080 1250 842113830 842113841
    0xc03250911030106050f070b0a0f2403060903021507020a021008131b03050601030f0615080a020d0204110c0a0b060f031207020409080c1b041122180519 67
    0x41c8407980420041003054000c00c0140310100c000d601c10703030508105465008110314210741d401300e030076110300358030036500c48900c200400b01420224030009025a5148032140000c94000140503603610500f01303080c14001c20400a241c1140c2d1219441d0340f50001c0d000791643d10001040b4040c14000c02c941c44018050101030344039045c1e2404040b541d140c0350311601d85040500140340c08500f4428800b00104406001c05030185000f8425800031004d60b00d403040c1214001d08a0040b50f41851a05120890020070322240759130f01224080c00c60307105400024010032809031810500c80c000a000c0e40402c9021a44c510041c2c0a1150040107603610410300c1030303140d034200e20503030b05030414180ca10038030079035a014284040c005480001d6691076580d402c01c5075400a103035100c6991081401a4100707c000304000e400c20340581e0180495004017a12500354001c0c850b0f00051a901c000d101e003031402d0319400b054014020a1984c02100c802c000c3c245d801803809440305100002c41001600003401da40c003c1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 842116330 1250 842115080 842115101
    0xc0303030b1813030f090807090e070e0408180604050d1b06020d0512040c0506031305070b210603010b03030f0a1805060406110a06060605190e0a05010c02030c032509 73
    0x1501c0030501c0344e5130b08507503400002c020041440130004000c02c03002c008100d9440070300207a0f000010003004449540b490301c50951b01c00001d0744026010407000490810540341c42112221410040052480003c3e4083c000ca8100e00e800c4111450840107100d052520795000740340076003102078560780f10348049031580748c0100083c3c0032500c10040b0040101000200da41d002d801800040c41e8645c8410002c0d610368001d4989000c04010703850149c0511205000385002011301a540c1e038a00300014084051500042c01110f1040c0c81c220001070140d00c3c290060080000018166541ea100c0504082115000085c20000046202507654440040340c03000c441507500c0181034034100752802c0380860f80c5c140d0143c2c004550f0302030801c400000410501450340503100c161100c0d6204c03409881400f040e460039120080801c001c80c1641011a09d40361145401d50301c084c03821008015050012130714245500042c40d825200b4000781d0911444442c1d807003109540942e951ba04865520780d5004d05542254a2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 842117580 1250 842116330 842116351
    0x519050f0402060f070503040f03051e03031005010e121f14060f060306031c0804120507020f04151a1815180109090c480c030c0303030b18 61
    0x2480c1c085504080c125446c4198107d23464151142e0a40741d00d0800e66104880b80e90062015681407582c00c076030f42101c2c0006500441c1180b52804440390740050600c00c5c40d05000142021520940f034910303485000c0c9078040300310380803442a884a54403507005d040402c01284d160101410382c10203110403e5000b12002080300007058aa901088004d90014080039030610481002000080d8592070040c0c0020040d00d031124a40742c03030300708596048801c818407000c1103410080e490044e03448801d1140c4050041d00c2c00a1010707140c0c0c1040460300d680b5044518841c0500480341900500750004120610044000c0c92000144c0002e02004920351a44202004014010300d51840701381d2084400c201c1c0149400941c180d42c0c0c43c414004c40350702400d03030000510f940580548406500c000007000c202e8091144005514800c900024100c0d6120780c07203821401020039505000b080040d01014540250031440c1c45a62071030060004e01e0807103005400358081102d0b00c54101e040c2d5100b103209261409 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 842118830 1250 842117580 842117587
    0x4314040303080a180210030f0c09290c07030804090b061e0304062d050609070c030e030102090a1805010f031a07031b020c0f1f120f0519050f040206 65
    0x980400a0f103a80c4107001c41d001d60000d03a4984440c12103a1b031041e1400541041004401e000303490b80d0a040c3c5081c41039281c420804098602c0c148242030f19444440907500c081c1c024031000701c2c40340e040000360340d00c00e0070404824803078203c2c010b00c121901110100000401c0c4001d10405000e40b0725502000003140b10000d02052540008513031051248000090701c51143d8102c0200d010f009a00100c40c1e91100c120b04403225051003143c0e08110100c030b800c0000c2c82c180400800848916000404001403010f400841c0d48094041d1000200b00030060303203405460300400c0c0ca50a103c88885004030703050500010314140010a1039081d40d410101d80c0300550421000405e03000c41c00f80145003007640d6841c0100055082040020413130056901038007400e140316040001414003148045c2c49911208560309084608142d80403002405040080c61326480302c0b0104000c000044000d11010304000405c2a2507011031481041d2408124040040740c1303c42100c4003245030125402500f158080 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 842120080 1250 842118830 842118841
    0x3040302010c14060403080a0c02011b0f09050603010e070228023105010501270e0c0c0f0d091d040b0c0c120304032006431404030308 59
    0x4030360402c110b41c0212180141c0e0041c24240502e45102240c1c1070b80061203500c2881088500780c040c11302d01100620003071205507a00560b42c4030f65070290482c0001c0c0300001130250031440c090804070000700401000284c403581d540b00400e0003108200c0d0500014020900810040201c802400d4031009600441c150036242d99801d0150100c8d0a01014800f082040c02c5e098080c00900b8004a11400e094000b080951400d0b00140c160600c0000320802542c0000c18054406034201d94001201e01010124a03d500c507080a03401c58402d540030500300340904200b1420507500002c410a070541d480d62200f0321256a01d040648240b908088100304003400c0340441e001c0385d0101c61140d00410303c141e80c01c0c40c20404600d114076107004c841c80e400542d10040104014907401c85800d5500c1030703900170100343d1600c6d504202c90319110010a4094800d2860503080103401c91880038012021004402d4501c56110000c007086c40e2041030640d5002031035000c840203d0031886000e03602103075070646481103a034442 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 842121330 1250 842120080 842120087
    0xf09060703090809031009020f100e09040c26060f07050307081837050303040b0a09020406030615171002031306090b010f051c030f0215011d0f0106020304030201 71
    0x2c03840140c0e64a1024000e1040740c0d64280440910390203082c03400070f034141c0c2c20f10601000100546a03203100d0144018800320064104076006450700007101c0310000b0765550301e1f007215941c0c02038102c00c400103841c9000c00d0700d03180c110900422240034881250707007507960162140070b0840b088803001c0008a0500101c1e80d100d000313000040e00104a20f0103107100f0700e42d8044051400044624040c41b07011809551080c0005404103400100703944c084148200c800c648405070303240310280000b0030544144000804040c3c00703074040500365500271310500460740d1f20f06000d00130f0b150140c0301c2001e101c4c0c101c0d000203800c03048042d44007030083d03403002809800080200c134800a4000600f40001c04180030090800244580308030000b4510926500350702d54101040c1d84000c0310180c001c607001c0d8004d005040b003000c81c28101500041e81c1340c0380900c200340c441c11007281001c44464203000e8452450300045000c052001444040701d1b404d88180603907076903601a10103600c1d028440c65000da04200024000741d4030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 842122580 1250 842121330 842121341
    0x2010c020103020a02070b19090e010b161a0c030117150a0b0112020c0f0f0f12300105030c0904020d0201180f06080a0b010f020c061803010e0d02060f09060703 70
    0x3145c0180c40e4029030b1031241014980c410b2204141c072600d01c880c12511550401034500c081c04030381084414640c100b4002448522400700003503000c9801704030a00030410341e0135001c0c05026840c3e10f1590b09003850070f00414503030000e0140404035042d4070b040703046400c00000c4010302d240320814001d08039110000301c80c000300034104e07100c1c3c1048400c0c107000b0014100c41c0010701c070a00040b00240b107103410030640c080c1004170540d0180c40d940c010342d004480443c0009040f44100710003018040d030f10a04081030711680c4113016420b0303800e03074654203150282e250780c400e040d812030b981076080d20f01107802c9404001c4070100450303000790710150644c14100503520030704500b403191500c4500a0096034030b46509042022251b03015800042000c010060b03070380d54502804c03070007000c00c2c00d0000380c0009a071000303900c81648540183c064500802c007400b0140400c03c08600c0d10b8000390003004810b00e1220881d490703c0901b0044000b5205050100d25550f546d20039051160010001900f07841d01d40d442c0403406440d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 842123830 1250 842122580 842122597
    0xd0b010302150705060c031b040e01060f03060801140105010201051807121a0f06011b031e0e040c0207030c0b0906031b071205120708010b0d180b10030b0901050402010c02010302 78
    0xb0900940000410402003207000788081c8901c0e03516440c04948035001021300c00307041c03040d41109000800c8000d90502405054444509120800900f01042100100610350141f03100c0d609010030b4682c0c200c0c9100c2c0e0917040e00c0b0280d000b4851692445030344284164090300800040d4490b90b0300700500e12500c0041e4035118070414110b480c0c40264000654202006d84001c0304403030b42c40e070502c4025a000011680a4041100c400d1106000364502401040954210081220100050000c62403150b018180c80140080042200384000030b0003e5940d49140000c40d501c910b0b01c1c10120f1020043e07402d541018000030611490340d9115810f81480c0c00d00110308904981e020b20100b00059004581400b61030941d0742e03941d80340c030140d0141ca140c0030b40c083e14100502c0000e1005021118040048400c140a000c002185c20444e2103550281c40308120000380c01000f05d10b06001150385040710341b508403070007400c00800031703200c03901c4a40c00ca44064500a0100e0390b12068900154000d401a110340b4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 842125080 1250 842123830 842123869
    0xb04030209060420030a0c08060d031b060501140112090f0f0c080d030b3f0304091b1e020312040206070f03020d091a030601230a031401050d0b010302 66
    0x740501224007021415510484c0f840807000700404c00722034981d100e155940285031030182c11030309000307010816001040c030024080142000c92051198405103145c003d00d540f01404000641e910b003940e90781340203110801400208030000c0d034002d43d03406020702104a03800024034840303103070b00f6525440c180b04040e1044801c280c03800800034204100313012140d004030498401040f100c0c047c0080090401410320010b01e100b5010b2481c035a40b60000c844001861400480e100000e41c90483d1580b07540200e1b8071040f41c0358141180703003020780347e203c500d44140c000d1915014146d1414600b4402c1d440e08805420f030050780184200210f0142d400b082640090025050030b142520307940f83d58114440700304007a400f5031b214540c102c200301c1d8480a04002445c444e58004144c030380b5208d0b0280c06110140145040280000000343c03802d4025811041d0131500110042d0380d40c0414601038090200d00424040e071500d06000010310341003092920000e03552110701411030380c0c06c603401c0140b100c1000241d201007 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 842126330 1250 842125080 842125091
    0x8120f0a0e0a18020301182d110d06080d0906020c190302040c031409030708180414090a0312110d0c050f0d14011a180d020a09091205040b040302090604 67
    0x62861140f004000303103040c2d120160381e175030402c07010840d20407002c50303220b04903844d00756031a15202d64080d217482444c41340040d0341003c010301c60f0703010f0141a0300001c01c03814076000198804107140c075500031011a03082006640c40c0700c0309142d064400180c03a216240140c5c01c10301d0103c0b0f01d89020385d0b0724030740d50b0380c1c1c0400c0f458095201e40101c0e085595003881c8502080d0340d01c1590240481406940b5408010300c0000c1d0319181043c3c2d6000310038000d803200c40085c00b4038140c00288542e1a90800c3c4c8100183c4141c107181490710090040c0d8564070703a041580401c40300005c0080031a25801000c81805031240414544408070081c0303130042100800b80010000240081e400c00407101d80180705140749010003041103080c42d03d00380c2010006900409551030307502000c007440c0c0700da4003d0b6841d44401000015200020901058844d8400b030b034003c0d03003c0c15018001c00c1e004c40d9607001d4480b0078021075140300f0070400d001045ea11031160780038201b140034060008100514040714455802407026201291 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 842127580 1250 842126330 842126339
    0x30711071706070e10021b040e06070c060c080708010605070f08041401021504050c122107030e0301091e15060303051b0706080a05070e0904050708120f0a0e0a 70
    0x50418190040000d5900120240800b00da40404504c500b20802c4900760342c000280c002c0030390f07950f1850b81411003071a59604c01040680d22603021000d508043c009442080c07a000e603001344503e0410740111085468420030b442e600d807080034554414100c50300c41c0260307a42000401d55041e004600110b81307000801c0403610005803c54040d0008019050013160900d400780006800c000c2c58a5900c820700f22401c0812001c500005100b118248060f5508082491003858040c10f0000078116051107454441800303c00745844402081d040d0f0103680d9840b9070003039440405081c0c4002e100f01a11034004c4075090a81c0d0902d46180e03036171440c4118031204030900c5030030001c3c0c2035640c82e0303005901080010828440e075005500705c1800310342403200504401401e12a024020f50400b407c404100e035540d5000031402c2c0d0003034034998100140146542001e107000e20b07001c1c1e51075509004158003800790025500a00460f0030070340e80d402504811603402c013200031b0821140801114180344c1d106182a00006 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 842128830 1250 842127580 842127599
    0x3021903051312080601020d021b06030907080f070611030901020715020a0605010323060f0406020a11031201080708030f19020705090f0108010515010c0201030b041d060a05090307050303071107 85
    0x485144444c0c903002841d1804000280c1004182da1041080d50052681c80b0480c25201301c1c40300c400101100d01030f8032a142d4968452400800e40c106012a200c1c00811002441d00010105c1c2150080c0d6202e040404003219100d46a00801c0c1c44640541d010860a0001c008420070380f113000300b0544100c03488008192510320a5905c02c3c1c2c4203a49008070450403d0002156001440c0c2000854001300389a045c802a903e9220000400103422554045550381d6824403804580010f800c1c3c0b0030849445911503414070304000e00070310a01c2c4007882003600008007184003005035242040e552540c107052000208410400c2c004004030301085006008002c0784070350750319031000d001e904d515800c41401c0d0305140500f800c4440161280007801201e034034246003a80e001d460180b8280e42031a021945900c01c502244c05040980f03800d1707410154940503040ca40300300141e01445032040c11400d100710784070f04001c1c0340c59124507035014000d03400400000301201d006550040039040e445046511040c1c1c0d65030b608 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 842130080 1250 842128830 842128853
    0xc0106051813060b1c0209060405071403090304030b091f0b010f03020903100623040510030f0c090c020102180a030f12090902180f2e090b0c0106080d030219030513 72
    0x15002921703440250029800d1502d5441e90210303007998108071034100400301505480d500b810091825000000250740000e080c4144c8004680c811100c112b41d003800201a82c0b02d03160700e00e000d444000000340882d0781800038081c0e1220031206841c0d02108090b00101100a5481508150340510134000d01541182c2d9901c00c0200501800f000000502c0c6844442e007540c02070b03031032030b5441181000f0500c44000c00360346480003281c1c3e1161b13028a00c0c100380d140c42d680c110400d5114690075403030603401241da160107400604817007000d07030a10960b010f8542c3c2004122001800064002001540c541e000180d421143c0030030080c460405c07503240359486102c1c1c0c050b40d0014201ca24003003888038140a03142003455001042520407600c01208114080800e04010030403040d2502c0101922000742c0524016803070140030300301c0c00003050f03524609002c019000e00401e102c1d504042c403d0040f039a643c50300c41e10954054403e14983c22164022001c012005810040d107202e020300f00032108240014580482d1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 842131330 1250 842130080 842130109
    0x1005030703090f020904111903030905010e040e0d0203030108101e0b060408011806050105042d140103050304060f0504060203160c17010c02010e01090f1205130b0c0106051813060b 79
    0x11881c2d51503547d42400004500c0c03801900b1070a142d41024400a500070146030b06441d000c0c60010080c0c070030040000c0151100d1080b10119001d0303844240483d07640413000314181c911341402c80300100d4001245008481030340d030500001d07007840c0f0170440075030005070020080004001c00150525440700c5400e82100d4012501b5581c1250021a84c2c04100325801410300500301103408216114030141c07001c402c00b25a080c684134890181d079140702140308580c40605a1400524084801e41c1c481c500a07903694807501800c4041841c260b20181100e105100b140e042d900305601941c1000503900480c643c80c014440c04039440b01d950a408203c40a02004d1842007416000011a4084136040b001e03003140c452481e0031010ba41000710745030105541004000e0703442e51040d107019224440710012101402000246c41d19889103500c002480910390b4041d200450200000f004110b0b40c0c1d9040059544c0c0c0c28a0729840401c86500050202c00140d00d050481d80c010030003c158016240000341244c0e0b080c000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 842132580 1250 842131330 842131343
    0x60709211b090b0a050616060b03010e01020409020d1a01020a0615090203040f020f0306061c140f0a031103090a0e062407031b05120703210b09061005030703090f020904 74
    0x1c0c1000146481300340d04004001c181d80d04ca25001d412050709548914255028044a44403a03407400980c40c25031110619038900002103441c0c6444040c100b001c2c0d8000005c8440c46400c001000c0d80346803200b00c4840b000c20058006115140da03903541c01e00900b50002c624010781c0302d0603000285035003c600007035104610801d002e8111118078410000c074004400c5499020b64800300400429484161410901e6440c03040505201070b4646400b42e02900c10100ea83c90700e005140b941d4911601c0000c100700081e2180c0c4550980300c4944048550b83e0151000d420760003204914200b10700c0b203010285036044600581154107105440c41c044400480c1201c080309042c60014441e014140d002c1c2c480590031445c8045405415140d803078907640c1d0040e0518040c100343d000540a000c15025503004560803a042d000e00c0710310030400c0d800c400207000e940442c901451016000807440d207080b4944101d108032030345030a4159201d11004030300602009004076480358103550f400016a8400e28080d01c280d06c20b01 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 842133830 1250 842132580 842132591
    0x27060f05030d03060b041e0b04260f06070c0311070f09060b04180c0504170109120e1e010c2f0105070c05010c02011704050f060709211b09 61
    0x4050501e80025202103100301132404c01c0a21080342e14004a400301e90135034140e44882421108161580c401da0780c803030203044900040000c4c242c07000c40e030850301420b00300c04071100d04940c45407907035100c272190203480071f09030060b100040019008000e8000c0039070080c5000e018812160b00124500709490300001e6a1404410041100d503596006030b81c003a03c03c0c10171050030a0328103082c500105c6e41120400e483c0a8236108190345451056055400030038000a01030800481d040c0f44a008101b44c00054030340012102d10b10305501e0241041e05203103000500300c0380d00c0c0000440c490450454404646040003420490200404c080c41e0504074241400c80d1701c180c03070610400c07500e54161440501c003818481c00b40400360208035840c991008440080c24a040001402e1004941400c00e085000341c1044a0701d041c0018001c0004161122340298800c803103442c0c03a031700341c2034802c421540320300c1e0404108455850f8103042600e401c2c010942c8240d44d0000548110103500d5030400864004007442d581c0e80 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 842135080 1250 842133830 842133839
    0x3041a090a050f011e020c011811100c03051911010f02090f030a02030327060c0309032104260715020d0c030509010c0213020a050702181027060f 64
    0xc1c4100c4610a603e9402004000c0d499480310219695180c5501442a80810800380703101007034002c04a180c440701030b000c410346443d1400d14006207509950034010003200640c100014014241c500040341c1640710103040c4035440c41c40d49251510403610300c041201d403039494004079000f40100d0401c00816000940c5640802043c810340745000044c2a109502c2002c880025031800b000300d540b000640c0d901260040c14407280d20400003c266002c6411002c00544080101004401343c010a5400c4003650290112900200c0380304a4250805940c80360070030040108207000310105000c21105000301d4900541e4504c0241401000d500c51002010310a034030500650303060008822030307d118200078098120949004245003d102549418004032004100655407005090041c2c0b08000c241590f8410700c8030b8004160b030b00017603030807070003450052a0346000c12180e109140c4240030082640d0003003072501d240301e91251107161907072320300085e94407543c518141300e40074a0f40908126095880714a281 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 842136330 1250 842135080 842135083
    0x21309020f0307120803040311100603060f05060307060e03100213080f010516210c050405210d0e060f04150e040c080c030702070918020102010c05031b03041a090a05 73
    0x41c009060702c00e40010100b0310028020911010341c0c035800c0f000c040d440b0b036141d14007a206050f44005403850780c41005c900000710001900402c0607a8490b010a0101170006c1101905842c003d4444a9154210031014032045126100c101070600b001411a2410b608198500c2c041764004882c2c040b9198142d1010f200000041011554600a11000300b03c903181011040380400d02a403122002c1204110004c088203209400400040e00308030810404084e84180c040e10071b6200b881014003c5816950700b114400001c50103900980c100c10107000412604081142d00745203003100e05902480070f10003414003d4170328000d00003414401c040c5656882e40036a028000c20002000e01d032142d410012180c00b0154441d00d4035401400c10000f00d43c5076140d00505130b0070b20300b050708982d150314070b00414010a24881310f040d12005000382c000700010355540404858500c0201c903000781c18014024000300782800c180095038828007a5010000f0340c1014135403d41c0b203a8056548013603591100f010fa0062190 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 842137580 1250 842136330 842136349
    0x90209070207060c11010c02030102120720060f071107030302100614100f020f160f05191518061d030706021906060314060109110913150302130902 65
    0x103980020a801840c100c0000e281070700c056001452160703004001001e50740141c801000b240d50080007592100ea04c40684100f5a20881d040380016901140c010202d03800300103407200a680400280c0910755500c0c0c040c194144000e4440030402610707503984034001c1c40c1800700328003440c402d5018040420401e000c0c4429901135401031007941803220a111500d68540100b00f4600a090504080c410151780050341000d040048011260044017492882c80e14020700301001d842c42e94160b900102d4880e8188495800d094801d00302000c600328003408821103203c00034100900c64035000003109120714000040003496032204022400850710392030b03500d0705407442510506068000300303849490500000c2d6150741c0c45c0041a18100304410010502c183c540122028580017108400038001c01c40c0801e964103424428503205600e0b1204400c500302c400b504481003150700a26848a4031040c600c04002404881030141c1e007400502c000100503220f5001c15880301124000018002400d03005000320840b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 842138830 1250 842137580 842137591
    0x60302042111040f0b120a020d03110a1a0604051f0915150c02100f14030c120109060f050105042105150a0b100201180206030912070501090209 63
    0x50050209001d420210729541040108080340c1c0c140c01c0c012414410008900440320540007402d045014005005640125505100540782c00141401c040c8860751a4084414002e621035064040040482e00c2041455188102c0c00103542e0104429a10001e94460038421008103c1d031200c20883c062800348100e6034000d41c4001c01000740c02c0c1040c01d2001910007801480a40b50765403400e030132542a01c1c0d400300050210385180f403001e0984404003402218000070100d11a5210207400035010348150910b0041c81299100e0100384208103100e0303801e40e000145800e8003c2c4d01407180100c40002c10150b00e000f081d118000042c0342d8140b000303041950040c0e410403410311400f04404c10004407001e6190803880702c4011454501c441d1407400d2402d05150342010090342040c8c00502403c4481540541e10100088452900507402d1741016402e98000c2c0d049020b401600c43c1d600000f41c1031640085901111003002e03107079170103204202c58406400091027601c0c0340c0c1d07480900c00704604054803a0b98200 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 842140080 1250 842138830 842138837
    0x114090a0203070312020f190b07180e04061107060615020f190c081213051e040902010531060203030115050f0708030c09130b010e0f0a031e0c06 64
    0x420301900425038038459888010403140381d4801081a83d032084c8290001e00c181c00c03043d5141210f42c0c00e002d421104603070000b52101030b62500071441060062821461581c0b420844050030303840d02074031154103007005005031041c030b8807030302c10050022900e00206a040e1240b034000403880d051503e140400c4450442d84015984403804801020100150006c090350104080316803040092816007000ea243c0c3d40801e00c075200707400700741940d903001401a0240300e03031180b103541409555604100c0f040c005410015445805011810928200368112000f61401810020f01d005504194040c0c01000d801168901252150340c044203c03006c0b02c510ba0080c441032004504550600205070341101460200c03c080c4080000e0440d968000c000c2690401e58014122075240d10380f5082c00313559039015022451090041c3c69450601c00c0581c4950754503007a0607590940c804000d08180031071950000c0c1c1003540b1611480c00040007c1c000800900f22804c00d0a544072060503e15004540116070b40010b02030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 842141330 1250 842140080 842140093
    0x60f150206071d09060310020a0f0e01020705150901141803190236010e011403010908160f17130f0515071103060a240e01090504080f0705011409 64
    0x141940a01001e1090f5401c460908072070322081c00113880d021800f44036042d02c03400400c21003942a04051040c001401603243c98410000d0342c4012078450b10f040c00741c607900c030400103222000651100c01808040606041501414040c1c510000c0b241d0441c200e500b6541d10b80c8200100982010300141a5880d03038210790003403041003a8002480c410380d9041e81c0000380e42c405001103100301c0540c00042d014000c0c50104800b940c54010341b5180034824043c0c2d28542d81c031462034882500301441036851580e00001c0c0c3c642405142e0003010100c80000c00f00795901784a1038400c4011800600c10001c15425015181d0b581700d0aa00c140050807d407507012200910034543c040059031103500354440d651542d00c24582d40c0b894145403510500101e4034400f0340622403a41009050b034a00c0d4841280409920261125109480d8000f0104002c034060040c0c1d00400750010000c090040e00941c0d0000e108003031050038981c45020111407900000401c0d151071303441e003000400c185131a54403250004012400b400b0f2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 842142580 1250 842141330 842141357
    0x20306010e09041703130c03030f0e01020a0c05011107030c0803040608060919050c250203010609020f0906090d0b040f0b010509071d011808010501181503031101060f15020607 77
    0x7040c880b03000d00741300701403000000518a20108040440c02d640c0c001b2207003812580703a080061200809180a902092440784c0d1b00c040c0d9800000d4082c5003950104c0d5890507130b0b0600d001110044400040740d18148070300d810120014200300d401c1800f0341344000045481c1c614225000b0722000000c0d048070f00801d4014240700322003113100210003884001c11008035080c1c031940104004c138415640e01c000d010f000201c100e00608618101c84843d603000f14002d01c07140d626000340404a00c40d8084101c217501080001c9901810850042c0400c0c3ca0004d11041c821841e58442003400300c41158116001c07900021080c0401007451842d5001d01400d40300840700349001e100142064601029041e0081401e0110442030fa10034040000801001106440b1440d901e03072825029000a000701c0c000c0c5000200340c4100c8204034403410507440d00140c601e2240601c1c50f00c007038448541d4103245018a5403140004182c0105425000340204040d41403102c10003d0004001d040000141c48001004200ca40c4c248 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 842143830 1250 842142580 842142593
    0x30c030e13021e1c1503080c0606030609010e07051201060b03090d0908010b060f1b0706120e0d050306060304050708161e060e040e031b0c0306090c1f02010b0a09020306010e0904 78
    0x1404000719400051720f0340340203072240840ea21036000500a150001e00f0654550001c200c0310300404090b0304588a680310400654240d03071100345414800e501c03441c010000c601e0000541035895084800004000340c41d00281c03012544111640443e561082c444280741c140d001c1d41c0e00c801480b0b041c001700500f40f05100000d44900c0361600070609000c003c0340040b45551840b2440001f02e01c220111403481d84e4610000e442e82c240c01801025075490300051a841d00300216002545c2041580c8040c074582d10203081021070303040036200341c070f032031152190208240908002d00700da8108007101c00703000d89142000400354419003176205209190071550400c481038210010b00d24540c012038004c142601100d0015285000310030b4001c1e1005c40383c0c03050560090002c600501e0102c810340a55015581324980b89035501e0414400c50703084005100c504151681072220400c50302450300c0081084c241000014820b5034480c0c004090302680041032081943c0c120210480c070410a450025107031406440b100e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 842145080 1250 842143830 842143867
    0x30306040507030b1e040614060304030c0f06090510110c0a060b01030902210c09040b0c03040606031b06030b0f011205060f180103022b030c030e13021e 67
    0xa40540c0e19880402c04060080c2c03c00200040043c0915001d000100c40003e0600c003020005030007149480004511414554511850020090403161854840c0c0c2d4044400d070520032000d841d001141c14550380011340a0040f4992103000303200500810103810f07203c60449055001c102c007150301c100000e5113805d00c08145031264940010000655101d0f000040c0d0240803ea030b0001c0d0b02011124481c4501e9400d801c04c00d107500c1910085461100314401408080d401c1500c015200c003101c0310000b412800b01d48011540301c2e1040368041901e40d80d0342d0754460b052240b00a00701880030006024052554107218080020008840030024030342c481300083d0054001d08411039401d43c445002481030b80390b11384480c40402020380043c03180c0d120140b090112040c280802c071b108001000e034600140d482c90354400d041c0900a1024a00c0040d143d07070940303604100c42011020302150070030f04055036640445440504a103040c0c050796404400b8041049142142c01c07429182006100c03c0141001e0404075 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 842146330 1250 842145080 842145091
    0x3031109030606131b020a1109011d040609020a080c03010c021603020108040507080d11010b0a0308040e1341031b120d0903181802070204090501020705071508090303 73
    0x2c07113426440c0135010300050304160100007a0020914905180c141d400203507410400d010b600b9010008101d0303002c10a82110a2181c0c60b00c9160031884040765046c840c40709900140304a900180c80907480d804691340070010307400114590040c948844080c2400e00898110707170014806000400000e0003150480d0105001c00703410007000f8000142084410800c038005007000d101110455215180b00034001c2616002702c20542d400c0074000700003130034854140d400b03403a4011000c0341014100b03811500002d00040c2101401102c60b840b20020842400561011a80341440200f186160101088035003a01c030f075010501d03150740d14040e03c1c1c0035408415600024041c44001805d10028541b180c40c1024951503004281000502c0e0131031054154040303002c00740300c0d40700c0c0002d0000d41d820042e515259885082e10b556203007900303403844110540c020305a81d480103000240c41d241c903407501e40c00c80c1c1000b04222600da004030400c3c84100b4242541c10850103c0d0b2510300d50a24180d9030407611703400040d28 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 842147580 1250 842146330 842146339
    0x9090604030f0309030e091006020d09080d1139010203030c0a05090a030813030b01141e0301020f0409061419030b070e03030d14060105070804120c0b0f040303031109030606 76
    0xc0b24005c00d407058031a1100c15400518074030040c00c02140b2000704c0d90f868450f000162003a02d06080d80c090190062340f08880c01030f005400c40d40e50402d07040e80d110071070015158960185034400391540404800100e8001d0448018090034240d44aa54692040c58500141554414010801404801011100403200500e08143c03119440c5010a0100c003054000030803c60000c60442806401001100d0880340035440b5184141d9a07182c103050b94115101e0202c1e00a40e40d0207400e1000448500b502034980b50180005240192804071068160407680004000079150001040700b11143c00c81420010b001b1500200c0c140c00820380b041902c1110b00c0002c00c0c614000e400030705030501500f01003044c900080d0942e540e4aa0780081c4000400b00884407512461061020075520351041080d92a420392250b502480c0c80d0622910311002c0040380012074a08503040c0f004600c0d00c04950117814076a01000c0c010b5265800c501c1c010b01552800019820810001d020303200b40f6030750006001c0d401c01030a49 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 842148830 1250 842147580 842147591
    0x20c04150308090a171c0804031b0305040b07050102041e050108160c0b0a0c0314010b0421021206042609101205010f060e03371704030209090604030f03 67
    0x101181c40203035541d2103100180d40f05c08401080c42c01c0882c030290b9034689000c164100031071003d0306440320041a507000d80000d8100c2001d400d0080d101002c00d00d294002d08246040c00d0356100c8105075a031150a04650303036500881c04122400e00011186011041200b455696905040000f0042c0b80010091100c1c00003680c546034030a406020034010070764012908104528080c6203040240040601140001c0c0c50043c02e00502c0d00d603240405d0584554010040c07901d80340c094503000341740a1620381c007002c041e201ca0400c0140d54080343c1480b10002440580382d81c0c50107080c1005240c000704d1104101484101003100090fa011040381d0704404100d82c20a0030340a191821a2008507000101c2180c0b40f80800102d50040aa0240703001c40c1d01c0c56803050109640781e42411788420381600d401c2c0b280e19004806030504543e503545c07010110250500c5490360600781d2194110b18465140800c408000041c080c03040d424010003055010b40d100c4001c20550800382e4006200001280d0041e00300341d03481 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 842150080 1250 842148830 842148847
    0x2070e06010f0c0c1a0c0d090e07050c010b090a09300f0309140c040c030207050613021c03030f1107020d02090606040302060d0204061115010e070c051903020c04150308 74
    0x12052100079003150f81d00403101903100800c90a03e90b01070303441c13a00c5601c200103204108908c5641140d00359140d100051405480d19001500e46801107801c0540300d540300c002e410314540740c9151461140c660424003088034045402c01d8a101c400c001c500011910000104140250341307094010b04008062401007110841d21004800509103928010f250001d9000014403031900003401a1401600b01c034104040c5a50541c150200d2140c5030004040e0b400120004050107451100068004d0000e001c2441e000b81c58000c0203036041001200320b020980e52090014901d41c14803c0e1000d2403d203844113480c140b0184c0014080140c20a4000e1040e861100050a50b807130700c43c156801194003502c81c03030f16041143c0c2000c2c065001402804005402c410b844661210001f480f80340d01605a401e9542503402e2201c8032880c2000100007106000c40c004800300003440c100702030004200e0102413020b0f60744103460700a0a14000f005d85510a80c20120710203240c41c403529020084a92005d031040c0d448011 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 842151330 1250 842150080 842150093
    0x606030403050c10090b06030703150908040503060705040e07090b0304150e030d0209031203010506070b0a29100201050108120304060b09071d041103010501050c070816030302070e06010f0c 83
    0x22040e843c103150041c0d1070b140880300a242c1202000501c070700c0c2c00348074a03030728403040c1aa140e0700303031001410389442240003500403800c0307511240c1c00c9c902a0804502e02034403080407074035000003610000e00203003001504006808a440d081601b20100e49001071001e81390441d900d580d40400781001d4003c1620030b00940110420b40d000d483c0c2c0391100401d880e16030029801e14402904094400d80c041d01407090381f00070346220041181e060310401403080c1e083c001d003034441200085c0001c101c49040c5070340360440302200340b0b298000700c10b0352071508000c81070050080520840a401e14240020b5a06060040c0800f40380440c100c440307500d80b02c40503600c9940b14181203000d400c000c403040b07402c1100380741404203c0e0781c050103580e0000c996038044030307142c054401030008a80388103420035000c000902c01880107604c50402403941c4d0725100116194543c440d418039050104903141d00e5081c40030040100100742c1c040c000c040c000e210429040c0201e140c12400039090400c0325040c0b80400c09803050450402c010b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 842152580 1250 842151330 842151337
    0x7060b0d05070803040f0e0622020409020403240c051603120207060e060c39010c030c022401050d0c0e0702010209120102030403090504052d0402091e060603040305 72
    0x1c006003100d403500d03654484181c881d80180900700d500d03e1001030101d0342c0e42801c50014080ca0703000d400b51003803d10b030362038420050791101040340c2c0c0650200400074000e2001e0000d03001442c00f40700069461120722102c03508100441064109450624072026105178218042e50b14051a81e4155003c401980c501112200301844041015034408680300d02400859484101809440783c1158442c0d1a084030445c10f90117400c280341085074040070040e84194060f20000c1c01c4c910403011840d01200c4601c040341c2940d804032250000aaa41c0c00146280c0794108800012040018103490b40204011286240000140203481c040e1001c0364156040100c20010300004284040034949035041004000307000c0e62101500910500700d10b00e0784210081c062007107900556043e118800c00074070b04400c0c00f0241a0003404070360b00c040d00b00009002d40b400340071003001c0c80019249040c4ca61400e441008040f44014011091411200080c20040020f072022190030440031030f04c158490340c841c80c0c1118a0320 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 842153830 1250 842152580 842152583
    0x1c020d1e081513090f06050c131e12030c05010c111b0616030903030810060509040e010605040903050714031207181205030a08070302090a090e0a0b1e06010504060507060b0d 76
    0x61a244240d01405030031002418240d06c508414130450316541090181d6000b9242040c00c1c00491810404c4250010410300c4901c144c0c201d41d000c00599100803440c81030125036019000b060558000c002000401c2c0b00b071916584103400c0c040b0014003050050341c1c0e20806034200ca002c034080c1c643c40083c1a035a45007130300e904c41511012040071104500e4018106403040c0300407408500610040742d84000b01005060664105c2d0b9522400e24003500100400340c0304241c0386800c3c9550f05c00c00440c1a40750742c091008400c2c000d80303d6a54810007460a1054440803502500b0355130400d1110003070309410180042d420512502d0141280c1030a020b249082c3e17102070740140c40c080320000d1b6031401c00a002c40a010001e00c251070f08003060741e50b03803406d400f070340b041064407544080e584200f0700541c0115440f080003640781c0012240c40b4102c0340c0e545580c4a80c1600c0c806120300803040001e81c896a00c00610780d002800b86400d40c1130901e4140c000d0601c0c0180c0030000e040e1170301c0e182940d84988071442c2e50940b05 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 842155080 1250 842153830 842153869
    0x8010f0504020304060f0e1605011b0609020d020402040902090925142203031206050901050d061d0309210d03180b01090b010201060518181c020d1e0815 67
    0x26847d00103015900c9107009a00c3e03207580d4200400107625030140203d45202110001c02202c203400ca541e038080204000c07441280d10541c02c2d046400961214409007024000c1c03807038016610b111800401c0340340c0000400000d0f107030026820165114402c0284a9003403c594100410715540e946120110740c0151b24400420568001c0809000c0618150410840b80641c49080d141c1071500d02c050301f503030007070300a2607041034868004001904245c4c000e010458041e1a000941442648201140110b40c03461200190300114080107613140187e01040000341115218100e10400e2a000703403541c00c10510300701032650340d252420111900400380b00d02d40d9440258022690b03102c0301ca120003007884c0c5000034010340c80c1c40404604c9080048074540c2500e100081d00c4c8503036035128140c10354103c07500c0b50007655001e140d11210088002910340206824144c002e0600054140001401e040c04841c01c0e100042003c1210000395400c1304d1301e00c0c1c00c41c0000100c0004051560089520241440f20b00f0340c82 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 842156330 1250 842155080 842155091
    0x21311040312120b0d020d03111f0905070503060103050705060f0c0d12061a030a0216050d080a050c040b070f020a0506040b09030c0301020a1403040f020a030f060b0108010f0504020304060f 83
    0x121035020008600c0040e002d142041005540d20501000703c40405c40250000b601c0d62800d40464050a0030140060418080760f0460551100d18021240903420710380c102a115203814003000b038280a8480034000542c020045d66145450b119138800c00d0380b0496004501c00904880650142c1044030380184050701203c2583c400c05800600b0711203501080711080b450018007061140040300c00d003005d00004201c1e80e0a540361400300d14001c0d4401a84551994601e5040e034002030424072078040444115140c0b00d003145000b5410b10107132600205402810780c003c00c024401c0008c1c2c8000d461006401010001741081c2501c0480c04010700f0340c010326070118010600103085485400200449881030781a2140d41d001c1d00c0a06083c1d008007404a07000c074070480f203950301c05e6403c200610352050003030004002110304d0b9004500100380c550002d44022034081034403814440b1500551504c0c007070030310f00060298034081b21044040001e02807544215000004a4140980354002800303002a20701e04000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 842157580 1250 842156330 842156363
    0xb0601141206010201051609180b04110712090f0e06210d0e101b0f2316150f0302281715060306061b0607020c0306040213110403 57
    0x840705000c803845401036084c04009000079912010112a080300784d190351101a00b81200b106460044503803620429940314804400340d542c2c2d0141c600c0d070080400d4041e542e10712904040d444180c0d980c0d040000c0c0008010b00304801103070028194100c03802c0c42d5080d220f40d161a0002035039040802031001c0c01000d0306825810155001c9a1100b000c03015850700c200c81c086400500101902d142c495001180108035071281b4210080786c884480d522410992000e43c2c0d82d80e40d00081103162884040545a038090310b001280802c0000250f400c5103085e405080e140b900800004000306a108d000c108101003940503c6c581c040e40548001e03d2000c2c2c020399401c030039249880e80484038031030a90005441014824030001c0c1e180502c0d0301034404c0741890203aa0640b04140180d0390f2000d88003a41101e0704104081c0a89115032104000da020310014140d5406c04c0b0800a18002d51000c503540310f50000d40900c4010790390301b180e4482c0103403031807408102c1c22a1020490700c1c5000b1035002402c80d8030010710208 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 842158830 1250 842157580 842157607
    0x30303060f13060303032f09010c0510020f0a1b05100f0b0307030b06090f0f0c0901140d05160f050315040b090403180e09250b07060609050619030b060114 68
    0x4948801ea840c20201140c6440842e00c04440b110311891043c420400c0020125488ad071090b20a4030f000320f0449200064500220040782d00070782490310409000304100c04000c0d441030f00702d80003c80c0c1a100101009440d21103540700d44001032221240c1d41d55448001036049103400c1841e111400605440d11030b039490900509000c2d0446410744617072501c9000554600740200c04a00419000084410a548282c06424030307512200751141400080640c0d00000070303001004102030083c40100dc54641088000b03105c3c2d0030b81b0151590305104d420302807194001da00c070f001e07a64400d40e90f81040e040c101411300030500800e61000101e07000308800d02004245900107408000c402085850713100095aa0381d001036408c0000e5420580540040c01d05480c1c00e13141c900e40040a204e002c0c00503401d10340c1e58241308403551040101b181c01c9a1240001c22030074440d40308650740050150740d00300203c4211303407035080e0390b0750540001000c03016010085403e90f4407039070b203582c220800e1940c284d075100c10102d40034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 842160080 1250 842158830 842158841
    0x6010c0506240d050f061806010b07080d050108010207060c0e011710080102070f0b0f0c07030804050f0115090b0604050108011502100911040e210d0e0d0513090b030303060f1306030303 81
    0x4160ba4401c96007c260074503144542c65214007200c0b0040d1030280d08104102d07806901603481583e501c00148100400080c1ca0310a00d030007444414001691150180703001d1007919a81c075504001e2201008001c1406e9030803018076104100e000f010342c1055516031070044801021030700320034a298804580103007000601e800b248403160003901c200322580d4032a90290300b4014101da42c80c2903c0818000800001d005080c846d821a04c10000d882d580c4519070b050b02d0846003594501000100000000c00c0f494000740306450380c106c8107030350744c0b40340504003400a0103100040c802c0111503d950a1901d0301c0c82d00c20302c003d84805003400ca05004640460410141003840c140c0014441d0340f820602034a80c50700005c2055904000c51a605a80e4080f0706200029400105519a50a88699040c03c06400500c198440c0a480d91039040d1180000301c5168004d0700c140e04440407441c41d040c9480120303980042501d81c0200e0840d4064202514140401e0500c0001d502076140b007402c24101004054154021 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 842161330 1250 842160080 842160103
    0x180c11071518120b040201050c1f061d16170403170a18030e0411030414011401060909090602210a0b030a0309050f0307080d03020a0806010c0506240d05 67
    0x80c0c00d01c0000b00e903030742c404101c9107104601e0341400b90400d0708002138481c20401d43c054014100315082016a0315524284050898409880442d00d0703048400c0c84243d11440019081c0090011100629095200d500810203071038150032040a041050016100b10700c0c03e40030301d4464280003500c1c2043e00c0c0280c0400c0c003103041a01030701e080c03c00244020050b0b20840ca1540c0d1102d580101801c3d407a102a508119001c0c1e009030095115104c0440a02c041401503014134800d01c501429045031051580c00c6503d00c0c0c43e40d145c03034032290004003c520340c0f061001c81a500140400104000c0a1500030028406d00c104000d503854030302c2d00c082c91048a80519403061901d00800e005004440307023055101c15004d800200443d002c3d400900c02800c0107000c950104002904039a101a20707802c4042c585880f1081903400290005a41e4421070f610902d503d40010080c2059000c084280d9281911a50001e0940c24000300358684142c001545002d10203001e0405028115440f113941801500c130400400c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 842162580 1250 842161330 842161337
    0x1d01021314010210050c0417100b040e03121e0702030c06010603051b03150d080d0b0a0b1803070302120115050a030f031b02210d09180c110715 63
    0x41e01110840d10404034030050303016014280d60300481400401c006400c00c103120f42d082c400440c0031601b610404031112110070040c103d41404100701c1013a140b2201c1400d000354148031100082090000c19641c0c0e59109048850541c3c4c1d03040f11451503000404c11840210b9080c40c1880b0030107402200800b1008402c20a07910316a0300c0e988140c2c01e81c0c0c0c0230b035010300300e0000b91620800559101c80145811041503825840402c0711000002d01e44c4040380e0701038441110010b440c0303082d00c0131072103000b046400c20340e00a0242440d04048a519020b0703084090a891030700301100e0b1081d90f050090b06d01030b50780207200c0d44100309050705950085c5400d800c03000e00c8440c040c00100300c1d480e002c260a003c90740d014010b1400080b0566045034402e084e101a240d555000c80745400042e07540d644e01c03901d90988408111864040802c070f9501c0c084000e2005000c0c040c1e6440c0074882c4040c080304000c0c0701280302c000480d00d014000c030100c5904413000e07184042ca0081c410f001c101005013400780100301c91140d4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 842163830 1250 842162580 842162617
    0x180807050f0609060720070f05120105040b0c0322080c0d020307050304140310050406091101080601230903070f081e0709050604020c0105100806070c0201020a020d02041d0102 77
    0x441c00ca95458060310360501c96070040b0001032580d0310804160041c498411031120088030944407141c54212940c10911804980f501c09018504040c96210000a09070009200d141030644602648070809003452180070000000a8143c05400302081440c207180e8151034603d600904140364281c00891642665000c2d082407400d03858400019110b09030b0304030014615041ca80404020300c850311a1541d60540074000815510340000d105a03072049004e14004241c40b105842d0940c6225030b02454117040c460b0b12000e0046a0342d2000c0312180c3c000d0031400201403030240c8d00102c24140103004000e40c2c035114514000c0350030400e02004000300d4008004a488080042007202101d0300c000541d03c156a10548081050b000d05402c81900306801900051400c03003940340c05401c0d11030442d203450155040980c208495401044481d9011070035103042c3c00c104082e980000d441e8a0041c20283c41b0318500301045c0d080d5a102e6012a01b4800303c1801d0703c0d10210945860b41c080e40040b468440901e80c1174 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 842165080 1250 842163830 842163853
    0xc0a060c030c0905090a0e01061208070c0e13110102071e0e0c0307021c1e08101e0e0c0f04060807020607020339010c02010614150a0c0618080705 64
    0x1052940f064600083c488000d039901c901d03d02005100c51540c1c82c2c5590349916000074100036409489a569000d103242c1039641200e0b0500d6005070b0a2684540c0b104698202004203c0058107900300d00107030f002c4102285000d4040041389030488940000e0300c0d07111740001d07071140c100c046100001140c40500810540e555401144565800100d4490001d070f0007449007140c1400d140c10403035002d00c07510304003a1001c07400b22011242a1880c54149008600032000f44040302c0f40000425000b8030808240340c200900350103c0784a0302005118040e00b201440300865543c0b19458150746600305424a41500c5954400c0d0040c5111001d4581001501800000c60302c01403010048501c0148896881c0e4885540410203210304504007610000600c40700426030350041080c06940000a4a0340c004603000b41000c1240c10442c429201c0e00e071007142103040d002400116402524403420751814006091083c0d0700340400508070b0604400760048207510340108000a020142c030079140203030101d480c0340950 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 842166330 1250 842165080 842165087
    0x3120d0f06080c2707030c1e0e040f0207020405100302011707021c051204080919050d030305060d0b010f0603110a231b0f0c0603040f11060c0a060c030c 67
    0x1d40c095580140c0000c443c10085050400e0b08a00c42019032942c620b5142c0681d100101c11042036851000094603a0544e40e281c5910080d80756150441356400b5034504510800030f0540c80316040c140e0302071500c03800c14041942c0e1660603151126006082804546028048081442d0160008901140800e000c070000906c10302881c91140000f60000d0040600846241844440070408e0508018007009400c00611040d018140244d22030303131410351643c4500c4200100c1d058158107460324a88500030400241d030340d405100002c0c0390035060004054503000e012412500b491013014204980324070000540200d50720030401142d040395010040d0043e40105100c051080003422310008a64828a040c054010b0002419010750381c00c00d02c0c03820024082d1805503071a904a080c401c0d80051950440c0ca1b4424001d204200c0d4046552a2075440e00307548140482100010180c0540406001d416035a102c1d441242d412100d00d00c00c49004c16041e1400401901c0000000030010703013084c1039680640e00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 842167580 1250 842166330 842166341
    0x3040603110703080103200414010f05061c020a0c0c030b0a0f050f06150d0e06180708122104050c01090941010e01032603071d03120d0f 60
    0x40c5541c0303c507196441c54881d20001c00a501d940400c1100c0890780c0b00311f598591143c14000354074080d0b16219585403901c032128030441b0f0350009015440070002d11140c50001d840200313000d0004000182c40315074076081103458500401004202c407040720408401d2100c1c00000c82c0c41202c20031005d0048541c0451074109903507040d0b8030781c0b043c030a0640200700646020ba240d403d90100d804603c50400036041d044c24142c82800110601942080d804c1c080300d180503402d9245400a0640206a0309103403200180e41c45c0300c00350541c000c54030040386070f0040b03441c0300b020f0600003488007005503042c0c205401c0c800d4541400c5e0745598003150501000181502d4207000f02954954412032030031410090151084c034694031105541050000c81c44100311880c070300b00645000e801c2d00d698a040d00d604524107000b0080142c090340c826103c80d1804054490391110880b030b0301044e00d1034581c40030700d800c1402a1317600c401001802d41c5070050707120100d54102c444001d01010142e0130030074031029000039a40300c220707234 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 842168830 1250 842167580 842167583
    0x6190209130903141b0709090209011a041e080d0201060f1a0708070605090d080402100c0302150117011505060706110408030c031b0f0a022808030406031107 69
    0x92001c030514001150640c8402e0003035019003088822400d88014001041d07111420280b0008010803a1100c0c0c40b80130004000548414402045180790680010f540c10105208050880211585220400701c05c4070070f81e001040c420800c241100540c1c60780141d521054010210030b88504104000d82c14414002c00b8100ca69810030000c43c41d08000040c1007030807a006680503a404104050400a2060070007803003c6c2c3c0c060540041c05080170144c2a00f02a485042e9400704410f003018000542d584009480100702103042c44000b117103c0380b03000d9060003076000000000e40031085c0000f40d00182441030682000032003008106605040810b2040b0421501565030407110a12640000900a90000300d00391003150602d420f066840c0560b034a194086c4c8020034054102080c500c058170906c40e030701d03080ca040c101d002e030015040e0100c20310780c1c440903c03034080c1c82000615204400e1200c901601342d07001406e4010404810344601c0700301d40d6a0300503c154800280390041c0c141280c0c06d0303402030700e081c0f5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 842170080 1250 842168830 842168839
    0xc031212230411010201060f031103061b09010516020907021c020102040803040b030a14040309140d051c03270c17100b060409060e0402040f020406021f06030b0906190209 75
    0x81e00e40341c5074025140c40f106101c5066650300c0c6004a442000750003064021343c0b18031100b00010340d06100303241c00d021000c0c0c0107203161004085c2c0420725005907000e48901407020718040b9100e00c0301e038200e52040340d20441c02a402c040c0d154184803000382d01203030a803900c2890300d684980c0340003000703000c034201d1180340718900c0241c10600c02071000103040c0c00195000394901300045408a80041516140c2400740c3d0214003045400d401000581841d00c00082d80400481d24449034404c175850307642d00c64030f4285a540300780c0d0b107030b21b01a10b105000764044803c0c80c550343c8501c040040c282c1d6601c0c0c0c0c04020b0010955007240710100024034070110364080140341d400400544040301d07240d070085020305116800c650340490107010118020b03d25120b00002030103141011186401d0074010b0104a903a202030454041f401004180642a0005209111003003404002403400f400c500401d0014840750300001d040c41700d1501440b00d4064001007050185403510740619641e809482c2e594100e100318005150031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 842171330 1250 842170080 842170151
    0xc01050c1c0b0619020d23030106031d16080c041506202b080105310501080607261611070b0a09050904020a0509040c031212 55
    0x300160450001042d01802c0039052030200b180303070a41d4004003610003006034004043c51200d00d51086030b44560654080c52401030041c1d0040f50030407440140280d405140c0c584e01d0a800100c0d4030310340c003034480d503400d41030751080c40381410079107118403d82c03082503a0383c400e98000c00f600f4036051051051100039140704443c41d03840d0070390a0783d0007014a0030845c00307501c1d60f039031089080b4000c0c8114600821083c1e4000d100e100c000c0c0c00701c000c0540200c500420005040010322003500d442c08400e03004409000421103a00100700701e2003800d0341d914042482a401d00d07000048048001900ca0f010308490b40700d4150700c008950400495220341c071000c0e50825010000b240441501074900d00e103a111510305810450b132256802c0e8904102944004041d00000410b03d414030340c406000b0300501000c58414200d410f00342c001400018040c000c0320701c1045075001041c200104804540000e5070712a0200300340d00814030001e8908a50005503210060411403208180b204203928041c0301901540700558 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 842172580 1250 842171330 842171377
    0x3060607111203130f1d0a05091908041a1216090e04050a0308010b120103110315280207050307030e0123040f0f06020a060209040b0a08030c01050c 65
    0x184468256030400032544031580030240620003000e184520b91350407413465103030065801400110394000d000310540c3c501e01504424500300d025030002521600801c0540f10740b4000e82c180041c0000480f001c0b07440400405c100151880903004036036400b0307516030b11225a080c030001140300d03401c041001070800d40b000411075040344554a0809166213868018030707032629029140d030402903600f518180c0c0801001010181d014141c0703809081b000d03a030b007820b054000410410140060000418500305107d2400c1039483c20001c40800c2080314000d501c0343c0c101819501c0c83d84501051501d4031417100440300d0181c100e54002c03030701c00c154040000d602d0301141d0b840c126080c46804400604005080d0440794200854581c00c1842071100c0600350340e02c074500005d81384000415405100b00f980a2801085099004550740030200d810000150340c51603a100064010483c0440c2a030740320034003d0700401c10300c00000103411190029030007000592112110103130745008000c04d038152261000030908 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 842173830 1250 842172580 842172593
    0x6031a040c050a0e090615010c030e120d081f030c1e0e1905010503150105060f0c030f0a0e190b0a0201110f09010f0f0c03030e190c050a0b03060607 65
    0x354441e000300c01071240141c41c1c1c030003d040c050040e440b00b248411044203101c81480700740444c54104481c80325600b003c016040010740082c10a000c050f041c000c0f01251100c09496100341250f0b60700b044000c1d01d1000b201d40001401e500782c02d4820156601d80c40d4003400a80e5500c906500940750498218402c8614101884c2d5003102c4140304440030688030503001440070820202203010f4642c03080b4049007103072040480300031100140e00540c4a17500034001c050f0490030766400d20f815514180c0f2403940d181004c2203840158840e00706524000e12000441a500070007040c01303070031152042d5803030b05112100c96080200507005400840c1d850746138400104250105030f0010700c0282c14900010030f0300e1200c3c0c0d0140090b600b2910030303090140b2001036400304542c1e01010211440125040943d101002d40b000100302116000004051546c2c80b41c40c2c0d004d212080000c035400703c00e0b6001e2030000a5079403801c952800c060744505070003400310758004100c5e1100c0e241500d21422000d000c0604049454940d034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 842175080 1250 842173830 842173883
    0x8040b07050f0d021b090f180322050126180c040612020a060816180509090a1506140d0f0c0b030603100903120c091203080f01090603 59
    0x45440e8462420078050a24080c80000340d40900f580182c5060503a030100b080003c07052911451203480b00008110991400450b8181c00030108040348500c9001c07520410300e14421030003003020442020001c0c907104101c201401b429204c0a076507491044030b4100060400141c81c81c0d030300780392031460400240c216140600000d00303c01214125040c03c072a01c1d02050803183d460704100d03d50200704a54100b5414000303910b1008180a1400034410301d048803d682086940440400401c9413941c405001d080c81400c41c0c00103808000c00501c1c0314103181240aa40d4110181d0407100708043c100794a520038801d22a00c1c003210300c0100058902e405100c01c101b08182298021500714141c003080070017044005081002401d21110819580e0400d0b404040c03a1251382900d9048050070400c0c3e950021b40d20100703421080903a0030340418800c100380d07800c3e100c82e03601790400d008043e9880f801400740750740074000d40e010700d0301004103240303a980303400f080400d980030750102030724415140016114000440c4240e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 842176330 1250 842175080 842175083
    0x91d0613051015050a050d1e1703010602010515031209010c0606090c091419030f1a0903130e0609070f091d090105180601051e042c0303010308040b07 66
    0xc2d82d49074010b0800b242c0445072054450801100035500610540c1840d45244020703050885401021585642d1903201c070b650301030038004c0c0c80881080d91208000c07003208102c2e4089034102c0090303100e43c1c566000034000c0c10304440d16075103203141100441040c2000728412441c141031010007494013290800644440341c5840c000c851f020b07a500c4001807495124415011300b4021a510580d4103403824041c24103011120400703a00ca01510a04020319001d1074808a0072264005c60402190810342403100c401401682d000d0101400c400130040c040c540800244540401c1ca403c64030340d941c13600310700c1100440c103e814035008a110804036101d2400341c02803031840880703447c0801c925910b802180382e054034040100e003040e4840f2424004100390a0082d1175000800e802048040c03038001c006143d40d080c06104060244000c4003421607101d000c484080c2e9411000740c420b200c0d84007003903142c02c409407086101c50f85080c4146122407070386402104480c101ca0b00318070024242418801c00901f240d005000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 842177580 1250 842176330 842176333
    0x2030c0103180c0e0702210d0e1606080a11030108100518030c030316020d0c021e12030a1b05030d111207120c0203090112020a031113091d061305 64
    0x88000048441800d540a0a02d003d460500c07400c1005c5c3c041d04e8207003036004030704d0181030780800c0403043c00500050314004840060003050304040065658101141a000240e00083d000d0020032200d07000100b0501498600380c0401c42c0c104c0047c070042e00f5000a001d4140160040c1005400313003025030b00415041440c0c62080c484007501000c0d2549141e006043c1c510880e00302000300a800e000c000d8032100b072542c80380050490041e04200040c0714040c0a80020312030088070040c2c2d0b0203110a891107208a000c007403c3c5000e070804083c4e0366903490304201c40d801c00042c1072541f50110607902c5c0306c0d098850303940040110304251154071001c015006191101c25a00b0301440b094403008484606a801604581c58001c1003500103e000010350b002c3c8030301e0f1402d5510401500507241d038855218403400007540c00050721b1705060f020031405002a6000a83e9a0b6000b0a1450201c2c100008071012140c0c00281007180c12204805550180070500361020755400002c00602d404840b103007152002da20510 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 842178830 1250 842177580 842177621
    0xa0512030f0f0f0a0309060b040504020612042307050a08030403152a031508030f0a0e03010b03030c0d0206071d091905010f030b0a050c09120c0a030f06051302030c0103 74
    0x7105050560804c0300701c900080c0c3c42d03000c080e0500403a0711884e02c0c840e40513201801030341b034903401103800d900c1884465818002e804001400f0710100d04211204522442596000960303000300103540e580ca02d000e1948500d80389030740007902c0c4500104803401c03039038083c0381800c44114110b007120007440c1c03440c1040f80408080600141e4004c00d009042074880d034a4400088581c50543c054101305856009a02c0b0f5a108004100e60360204005540c074441581c684159441034600220307004d01800c07440290988030200304681e00301c4021408001001c4c856088a059640380f00b0304980644e240303000f0002800e01584001e106042204450f940070669a41201c0b034841d2500d410300840d03100b40e010300d07140319898800344201b1441d070281903003003c0900424001810812240c0d400f0b80303d003500691186041d1450700c440a101800700c122401d00042802d0001c43d0749080148100c100814201d900c80c0c071f460000b50109007038008514405401074020300b41c10200d0b10054004000002c40ea00001c0d0b0399a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 842180080 1250 842178830 842178847
    0x5030607051c050f15040603030503060409030e0303041203080a05161b0b01090615030b03072106090507050a081f0c09030204050a020a02010b100c080f070b0a06050a0512030f0f 78
    0x1801542d000d0070409030515418a80140c0c40340c001d8882c00c1c0046e10581c1003020400100390311009980e080482101d0015203448540fa00f550340110400906406000108000903004600e09100c00f841d40070340c490341c1c019603503003021908841085420070b00c1c94003203121041c443c51044440fa000d002800c3d18404000c10662500c00001304241e00a281654070350f4810310141013803000c14030708885070381814000000e03442c000036111811401000c2c01c4051151070344124041245640c070905030086000c201d03a0a240c10300e1074640343c103401100d001c1c2104002c000f42d03404001035a0650800f800401d5285440c41710700e07201c044c20701041d03000100300d4480c1d000320142c1d65074800d8500881045400603502c00300d450000c1c1c2922071442e001d9110f2040781d81c1005810303401903600d54005a0100b40709507501e8049051400e40d00803044040c2846d5004000c004030001150f20410507114201c540014641c1d5402c20820080380a01c8502c03019041484084d100000301400b80c042c5554a8208900b44160b1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 842181330 1250 842180080 842180137
    0x307030c300c27020c07210b220b040803090c09060d03121d03191103040b07020102030f0c0c090f27011803080f0a05040b0613060801050c040914010503060705 70
    0x116107075244030b0304440001c000500c80011146802803031a00c051f040d078281364941918010005113481e00142038807aa007102c1074080100b41c40701f1948040450340b9030425061071821900b0407180c40c10f86108201c03020a039403500c45542845000006c11010b2085001e82e070440b07000d0700d4102071805081d1203e00c642c3c1c1022034000104000f41480c8000c54072204c2c20070480e20b5005400e000c681c2403041d1448550800b080c040200c0b010f89110341d0300c0640d13400c81440102d19512486410180c2400049601030365042d02040301c00e03005400700d50b06180354071240f103148200e05041e01c4e03560600084040b1241244e0488150700240003c5900005002200207090100e1403120703442100012424004c200c0785100d03641c00e09410200072481046140b40030365800c14004030141c2081e109049103000310070015056003007903000d020b0280c003e11045c2400d0703082e85a43d400c5400703035100b0b050130541d2002c211041041c00c9412660000e00801080d140c50506079069400b0300138540e40c680071403c28200703441c40c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 842182580 1250 842181330 842181337
    0xb0d0b01020c120a03090b09030a08160209040602180f0619050c0d03051012030f0c06090215030601030b030a0f020d0302030c030f1312051b0307030c300c2702 70
    0x3c1d6100600b010500307034a8004c14031491504903c00d2240240101e07513441c0c07000100d80190f10b0f803200f106669155071288940040201010081d4002d021000700400c11017030390090484843c0c5030044c551044000703400c01180c070701e5a00820340c0200c000e12001d011003030b40480c0950509040d00f041d03450046038503074035401d05010342080c901103600c0b80c061100e03000142c03038020020100d030041d1038480d500b030f03680061a588070040c1000400040240600520030158800b0b13018580c028011945080950520b81003500100d9903035021915003044000a802c0c00b18420740c0031580a4511400e4004036420031148460703610b82981148418002003c0f00381c801c10040444206006540b91030b020704c00111031402c0041d82107251280000107142000410024080d144c1502919044841d541c075a07020a18180041d440a4010b01c03a0b5803000507001311070b26464040304250b02805070030304c0d5407142c03400180000c0900103150900300002008079159000480e400180042d0030445205000d114507010b80c1c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 842183830 1250 842182580 842182609
    0x50a090b1906091d0d02150718090e100501090b0607080a17010806060a090603110103090813090518030405100f020a021807120605031020042309010b0d0b01020c 71
    0x41030301085040c3c4034003005894910800392000302143d28087e2403011182c54058941400d01038504840d8190181d85200100034001012080040d95000300703030725546921110f480b00c2200d181c00000304405c4554040e1001c45c10303001d010f241c41c0049590341e144481e80214048410080d0842c08c50341240d250b421054001c2c46003600900c490b040c200100008001194018522546003a42c20000546002803107511000300342000034141c0003500f40119140f00d003509001c1c0032040b9036070229102510b50311060180c480c00e049400703116940d48259640e0321441c05100e5010b10700c2c0d00c21510803031180c00180e02c0540705106803414075001d6804607034080c00d050070003481c504024040003051540030360a41d03507110443c4000e020035882c100201c1e0b00c5410042541400795101c010500c0c00706084041a120311800320a01684c4603911a50b801c00c0a40244014001e0140d80c51000c07003604d403504520341600c00955505141c98001448007000f04886010a810750144800d5080d46954110b071514000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 842185080 1250 842183830 842183861
    0x70605180904081801080f01140d02120d030b06130b031e04030504060e03060f011401020111040902030108070902070203190f151d191202120301080c04050a090b190609 74
    0x2140404c600d4400003524100c81390410000100308410520306081e00b03411107494250209000e094500031520550802402a40062180c070000d00901c800095003962550995010440540c50408010362486007800300d50b0b8404208000f070011010510003540c02c000e640080c3c0e1070001c01c0350010003800c00c0840301a000300d01c01140401020340c00445230882c089d4210050002c0703150444070b55882174411f009945060b50208409403259000f54000300c0e0240d1320103d000d89440d928070541010790b109016900071401910720024209200340241c3d00006d90041c0074200c2290140380900390011103000036500c1030140d8000c000403c8900240f000240e20304207000c90003140d4501100c440600340741c04030480d03601049025010b1103112100c4501150710090707040704407441032400c914100704d01c1003002414000200024004400081d262242030042d202030009980380800d0b4411a5140d00024100300c03044000a0300091048000d10300e100d500900000d48140c6400e0404101c8041000780b0030b14 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 842186330 1250 842185080 842185087
    0xf0705040c0302160605090309090130050c0105090d080d0b15040317090105190e03062202150d1406091b0712090312030203040b061207060518090408 66
    0x8905050094038084441c40c2000c0d46089540041c11414480c200030282440f42c0c2e41010514100c000d02c12240100c07401803c1c0f40055131985582c45111400581c04c903c004161405420784201410f1000d0f181c41d08400a80a010f29010054401d81d210100c107903405024404003500044005020300b80704c034542c001c006030307603404501400700e110000403100640d43e4041c00200b000071404082005080d84c41080309841c1c20022005a41900410701c0710784000c081050890185540801120440341f81201158840d0f240c440109105d0304990b9120008a80b00c41003540c0942451000e5410758104c1038441868142000e030440c0488414044c000c600c4948001404110300e00442c040c0e8110300310f49001c05007480018284e22452050030002015001c000c0c40e440d6143d40904002401560041c0d110300d1803200c1c00b0740c020004d41c0110b800b20752070030380880170440508040e1200490741d900d540040c80210704101064070f00743c01c5102d41443d044040e00608090352156412a401180300309025900c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 842187580 1250 842186330 842186339
    0xf1b060b120705030a06090602040b0304080c1605011e0c0c06020c0a0902120f04080706050a020703120b060405011d030f010c090b0f03221209060e090609010e180f07 73
    0x764a81c00007000c0210b0b44800020702c41a503010541100007030b440980091983c0701890520080e00456002c982c1d000300100411051104440c010b004035103112041e01c0c5c0c0d960700146580007010071801800e001900740f039211203e160030056482c2141c20b1506210410350515521703003072604001e03000180140c00c001d0340c8100380e0a003040d41202a041c1c5460940c00c04c91304802c1a10041c00062041100c0d0721544080f400b03010140c0c2c121080315800001c01c1c841842d20764814006548221021000a4182009076094079018490701060010050a161903e490000112030780c0a02c42c000b24101e802140c4008000d60b010001540410541c2c40081282524482c014180c03070139642c04020300d401c01708241c0d907080140c03600b16540031701c0d004c40d0420601c079201029081030403600c000a0080c0700480700448219000700306c48089421550340c0c00240c1c50b1035401c1c0032203090140e40d500d400004040c01802401c0c20b00010a6100304c015005100612995502c03500d8416082c140345c0254001d10800c2c030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 842188830 1250 842187580 842187589
    0x1030210110d030c090e041a0402060d15051e0a0302040e07050d110307060f020d0516050d0e09130305161115181509010c0516030503090a080118030f1b060b 69
    0x200401b10412001c40300e117803584444c0c6028404c4809105821000c1e00001c0865507441c06071000d002540001704040c203041a00d40903862024080c41b44910414500b003001c0c0e10240e40301c00007480002d443c6010862541c0e0902c00600050522280c99014118010517140ca60105007200d150180010140c00340481e0140350800b44160020400c1241600843c4440c94000444e83d600e1941031501580c2c403901c40040445400001400800f01e001307900000640b40c0d80089500302d041e5080f600702d00c0d6038880c00b006000c060141e210043c04902c050201c0481c0d03510316028109098010409455840081400503009018036061045040000b05501105040350b500741e2880801c00d543c6d100e038001d82c80c08043c03400d0140003940c904018182c00300c9810010144401c0d10211001d0700111203464603403802036200d41040c00701c1801441c4030b14001848250500581c0b1680f1103200b041383c550801c0f03480031208884040458402c0c030501801503183c284145081c01e04241c058540010071107001010030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 842190080 1250 842188830 842188847
    0xa17060a05030a0f050a351e090a0308032502340b0307090303081005010905090a0b090f070f08010302090a020a0201110d0504031205010e01030210110d030c 69
    0x9600440300c9080510050310001001d640458000d09440704a18851802a107071192075100180345001c1c480e2141503183c51400321880001045007094080903103a0307421040350165000d44411540171b8540b0482030410301004102120001d004007058644a0301c0e2800c0c031b680700b034070141da04120551101500080409040d120070065202030003c81190341810b0b100d504001000031a0160804214182c10004440b202d00030700c8880c030825120b282c0b0040c064124001848241c0206a404d40003402110401d94036030140d540c1610756030010350400c024450208001000c40349429590000c00c0e4803995202038051241103a64409049454030340402810b40b080c0305004814021014018401a41d41030202a4010303c592001626540c071444128050102080d285000fa8000103518081c2d1020360001d0b4856802a201c02440e20160080001220024030850320058010380040c0300514008025a007291218503000941c2ca607209070590030881d14144402c003096441a111000c40d8202202 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 842191330 1250 842190080 842190091
    0x9060612030405100516050601080c0112060506031501090b040308040312020a020f1c08040b0409060f290d0f0605011101180f140f011428050c0c030a17 67
    0x185042c645020007142c1184c038110211010302c080400c0a4003441440001804050340000c1140c406580d0340030450303100c6040c003844c18001101d00350302c044580520f000b180201d074409040e0518698a5000d1851048190f035183e0741000b2069400058080d8030f02d020b000954011384c1c1c1599140d00c0c519000c05001d85000d12002950400e44180b17015a42e00091004404025030f440e0340102071071030a0300c10401844000800c400c0c000300e000308407150101c0c064820748000b10010080702e51180070043d099816445541d074000b401886d40c900620840180494a1820101d45420040000c90780d40584109040e0703002c03c942d4443d820405583c0c8003058041818003003000304240b2603201c910f601c0241c00444041d082c0c00041c1c4007181000b0101d19200660002c5a069408400c8080304e414041c26503411030000448101c800700340d40815405121098400d0080c55207080498001004d0240000038040105d0803010300440d040b0b03c0c410710090442c218140d90b015907028604401401c083d201401c5c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 842192580 1250 842191330 842191333
    0x5011206031e060618020d05070306080a0f030504051c0b160c1b03020d03080106094401020f131a0403021c051608060f090601090b01030e030309060612 67
    0x8003040841e51000100124619103512280700c0000b9081000c090411580282074441400a020080101e1075000c0c020a0101003c00d001540b902c85048060300d09134000c0e284550003c451602c001107400d800720030010311900340181080c0e074660008000d480754070303640e040882070b101c00f0308100000394152950000310b540c0c1b400b8200070356410050a050f84e000004040f90a00040c202e034041070880300740c0045034010240602081c142c9070050800d4002c0c4140e401107a031105001c01d00301448940c141440d0060115540031515101c0c6460b40200b105400780ca4040f0b80d482e074096150400e00062103442c905540c43c50342e0302850001e01c03100003010b50040d500304841c0d040b00e1100c0301401017190304580c1c045640b42ea03a20500c10003000907002e010700c0100284507404400307032180d20104010084801031070035140c940e61010705407440950115142901d41d0000401409100026400401d40c04c006141c00240b0420300600d1a01d558829203040c0510703401181046000d181200c10340b15450000300 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 842193830 1250 842192580 842192591
    0x120b041515030c021c02010204080d170f15100c0c1710020f0a08060114030f01060806060703022503050a081305010914060306040b030d0e091006081b22050112 70
    0x460080d254178415400180c00c007000c43d081c0ca40d1034400d405560151040100341c40c080b0400039405019203250f80c04400309410f04900069150b14881c5123184900c01c0301e820b0700c040a100d03108000042d40d00d404810b040c400d031003201c01c01281016100d200980041002c401e402c080b416405494400030081c02c0030350500410000c040b1031060700c11f0b074401c440d035810b02000c3e80d1075030300c0143c40c01d01052030868210300002c820802e907202c0009a2604844144d10b07040c4d81a00d410041c8251803182d00c2000d000360380244500700507903c108004110001180c0e40600c805902c136078949062010700201a10144000720750b08655402c0c803021b0400030315007420b144601c07502d4283d03644100074075012124484c40012002503134548a6821001120318000e0603030380c6d460006070000c0c1c6a4040451060700686c40000003420409040c80c0e0001a40c081b51207612540e6a081d21513030101540111f524500c02040c48030a180a40c0702e040003010020070740b001256282017030001861341588683c9544401d0901c0f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 842195080 1250 842193830 842193851
    0xa050a0609060b12071103210109060302010e0f040e1b0901080a0201210b0d0620041d1509010e010e06150f0d0b1e04150b0a120b04151503 61
    0x2804640e000d00800c50140101c0ea00c080b019205d003c22580306d40518040011004016400900c010b4144003029101100f00d03621451507100310b50882c00002d011521a103c5415a1700e0895109030709030000401c01307d441e954100c103580c103103550f032202001041d0290301c1d000140e02d0413800c214003400300800206000d41f810b0700000e14a90740516225a0908110544401e001d00c54100c2044240d010f00500e00a020310703d0108014520f4546508001140840070f5200c1121142120704a64008085012a00d2074190b010a80080600030540e1113084a9a58140742c8400907032600800f02e03090030100075031402621101402c0000c20b5180306040c1664201030903141041500c2c21110880e0301c00d901c0d101c0d0401040010b1102d11100c1c0e6100c3c80040f00c0701d06041c1a10240045028166000d000900d0350300380c0c1d541c04e1092801459102ca20920980002c2880b980d0700c0380f103d0700440ca011820b118600c02150850b100c00907050b8903011002800d20840904078481170041350145000c010940743c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 842196330 1250 842195080 842195099
    0xb0415170606010e0907021203040c0801051302131e06080a0b01080d020706030b1206160e0103092607060c02030703080903070c030308060604090f0902010e01140405090414060a050a060906 83
    0x213640c0918070a442c8180803c8040e0300c01c00c2108400da81c255501ca603641030906010085012a215080d410760920f00000c24005006140ca23920f00c3e0301410180406009000c0721001d402d40c2c4078000300d41c031144603032084e0380381032070061400609a50300944a07103c0281030205202030160000c12540d40a4000203400302c3e80002c00e103007128103a20300000c6800101d07001624101051104885510441090181400c004000c0351110505621124827080e0720a005505039000c405014110381801d6072032043c07000401820f07110000006d003071140790901990f1038a0498501408403001a8400b080503804c06802002254000040300c4c01541016038039075965424a9090000600f04000301010607070540704c60003a507001d48005041840035200103807180004050605c42a03002400b1101d04290950080486207611089844c01038585400d1200340042c81304094421220100c41c43d6812214003030030700c0aa0b00944944001040174184240d004041d541180c0142c288149401401c04c100140c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 842197580 1250 842196330 842196347
    0xa0e16091413150b040e0601091518050a0b0d06060f1a090d02150a02011a01090e0c25050615040209030312060a1208030108072304020c010b041517060601 68
    0x740514400c1d0f9030000302d100a409030030f810040710b4000e4207262441c0303003001d80480c070a4142c4580d100d081101446c1c4461803036011103a886551980014540941c2d40b4030819001640d000310b00700e50200c1e00340c1c100000b042034150602070540701316a03190401e1103480e81401c0c07518000c1c0340100142d070340a640c00d06400d40074400c04150718410a0010b00000454a541e0080b4030400052042d4540356150765101a000c4d003200c00700c00c0305c5903407013000e00c4050b90b00030407216040c2c0c0d040c07108180742596494100250390f44004080c2a8030b07420008003103080d1380102c404440e464030480140449040110241040f01c10140b062445603005205030701d850b4074008103540d810010341c0640711040d202d807004541c0600c0b540d0009a00d000014644109024040000354100e8000d1402c03240d10079614000140400108404811040c0e000d180d041003070724080d00901081c3e0320600000034801900d81c001004c5078600090440b0705104030100300411010b00c0e1b41481d24a107a0341c0604400d1600c1070008001c5030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 842198830 1250 842197580 842197583
    0x7060309031b0f083f0112030509040204030303060e0a0603080a0c0f08070311190b0105060d141510020f100510030f0803060a06260a0e16091413 64
    0x4020b11110018000743c0f02d00c10040e00d4104003495039070800301c1d81c00d18000304152070204249054401001054103000a50003100010700c0000040740d09001e100e2a2200030b058081d000c020050001c00515a128802040150303c42d40740060450310300749407d801c0c003030f0061031420000c2c5004800c0002c510018100e4660700100d14020080820350f00d440b40650b00c0382c1d6009048180049422010035402a4651f0b1010702c00108503075514141403e5074407469401180100340b0564480104100d091031005410200c0d0015004140301060000750042d102003141d1101030010121103058441c14140844038542c00703648050055414404c81e4103aa40b220400210700e11075841d4001480c806002d02000065a84010382d40c08982082c00d0003601d41e04207403085441151240f40000d1802e00807550070038440703034808408032480b81b020388010600300014200042c0d20b0b1143c0c070001c425103051001500910006403412406030408241000321004c81c50031040c3d207111101407202036042c88500100b0203 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 842200080 1250 842198830 842198867
    0x80109180c0e0702192006130b09130c09030b0a091106090a03080c0a060501150c0f080c0106170d0f081305070509280c050f031308070507080706030903 67
    0x20f8955020403407424058000c151082000070001104112800e00c0c03580f02560a0158140944210f108110725442040c42031010012100001c2290800c6000a8400650028030b1401d0400c00d48400d0810754004009441c00207404100500130090710f070f0281030304802c0e801c8081002103855911804242003a031509486040003181301035407a0b50761200c03140516813180c80c1544440b40c500001d03a0714540c61100701d40890070000045081c00b02c0d114204c600194655545111052544944d00d01c1c2c21000e90070b031128401000310f11680e540c04d0280c4001451444840a00c0001d046421820040e652030040100400a4282007080da0b115440076004882035034076541c1c5c0030130340c81c007075141088a80c0110f4100074290100441c0300b241c40c0c82141e50056145d4880c1c4140005d100901c101c400c102c2c1008003250060101096a40700c4601039588071700140b051a01f15036280c0c0300c0000d180c001e00b1007100d003648200410700c604002402507000500385400c2c01e11410110b9075004c0d003244441214004d14 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 842201330 1250 842200080 842200109
    0x20315010e0d02120d031b08010b07110a0605041d06310f0608010b12030a110106081b1801080a0609060b10021e03130909080c030307080109180c 64
    0x640d44035030585920700e0340248403d03050101c0304e503a281c50b40d01601101d00401c0c40c10b03a68030080b80c040c42c0a02d6000f1010342d580d07207103607003801c07621195608940e00a81d80c1c5075201ca40321485031180c01600e0090143ca49459440d140342040282000440001d142c5512a0480074408642c86001e07040202442c401840c5005041c5070000b217003002c154001d0f0301c2165007400d1203040e0404e1154419400d8401c800e0092044484960134003010300d1560f00c486000780d00402010452500c00c3c2240422640b00d00300200d0400d5480c00c149150080e19004c0000e05c64847c01c0039200b43c0390071300b400007000c154156510002e602d03091699071103030300c0c001020345410384a9449104000055028101000c8010300c000d101c2d41000000a54540c02000c0001d1184071440ca01c001d034000c000b00781e0341c4084c85155454441414902c0c8200540052903088800f08001c3c410362400f400148041d5109441c00e56802006601d44007810742903564260580802c1c090042e80740000ca80e681c00b94a0940307400c0544d5208 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 842202580 1250 842201330 842201357
    0x9100c02030606040c02100c08012408061002010213030507050901170606060d0e010516020709330b07060f06050a140904140a0302010213050603060a0e0a0204091407080a02031501 79
    0x101f0404c945000301841c13600303220f0001d02d074000450300d068600341c01111140d0980c105101d1040c040030503554012075140380000d901d520b4240c008040c1610980300250500500c2e110310464805030342c10440b100c2e000341c1000d00040c00c0090703006006141080001d40405000f0106540f07980c0098142d03402050001202d203030400e5141c000c0c03000190151b000304404e28001e56150381080340000c2050050181c0304002680714203502035402c02c15044035400d454803510b0958824050403980d070000c440a6889000545409401c02800006000340408180d80202c5042c910448151b5040f9a1244800030424041c1101e1020410019801030381d203280c2c99103036070070000d80303109001800f641030f445028021070030140d064000c1d00100f1100742041c04075640320300c204511400121181600b0000841c4200500490303811015005043d01c60300518150301c4444135810b8540a2a0550312428076805011030241c0c40070708142d001380302c000b0450440c189059862b1044422521850410070520503240 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 842203830 1250 842202580 842202583
    0x6080105041a1c020418200102010b10120e031605010e030a0e04020306030c0406140405090d0f2a03030b010f0306060926100605090709060503010603050c1b0309100c02030606040c02 80
    0x5111b02d4181c609940030401c10b05c2e0010b2001c41752520780c6030500714403a00130f45650050207408501d2800510000da00682540d040300e0340002005c00b00076141d11074865a505040c10b000600341401040f20009400321582009400d5803550003020919071b00c108840e00115078050160726081904880160f5603071502000a86007203201314800d42d020745804030010300380c011405100003500b0b055405200c55a40c1001c40c2d91644000199000440c507000300c840d00349441411040420050085a10459080328450004a481c100c401f01c0101f5942d6031809010341e081480304807560758904c0c082c85001e09060005110140310304c9039006803a51000303125807580c410704901c282d4008400407100c2d0782200e814100041c20f0b480c45000c2c018100000424500791107a5900030a0340c1c0e59444052941c1d180010440c01458010008110914280411000101041040c0441420200095440325681c2040000b0000c4204015041c8909800d00e4001601d0110b02c807075003d03004460020f600901d091007603 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 842205080 1250 842203830 842203841
    0x304050d0f0224040812190f020f0f0903100510181a13063308130210110a120e0616171210091a03030714070b0406080105041a1c0204 59
    0x1a039502001d4801c000501c0d00300c4900c41d440b400740a5007840b460181d500d0600491003004903903400c00030300f0401c0bc0140101c040013010312844c09400c88030703070603c0242410100ca0068ac1d200709401404402081108050440ca1501d49101b01c0300f009a40c0d0084030781400d14036000b80c4503019400078426022000c80a44c044001000141e20b11044403076458a40400402002c3c26244065501c5810a1270588150142c600c0340300d120074261041c83e0039408000b190b680c0e0750000c4040000fa0504100b01c50700900002e4492031091442c400c0545045001801c0303916a10305290260605000424080f10100e51881541e500309a01601c0181c6404001d000707031050700450800c0d420481c0500011300c0700b038254407084800620042181e48401c1c111088003043c01e00b1115803540c002c0c8204000304012149408441c00102c08560905a0b60100c82d0802e4005030f021801203802c480040015090501403201d803c902c14231661980d8011800043c0b20700c100404035000ca03400500035900b10745440e80b11 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 842206330 1250 842205080 842205097
    0x1908090a03111e0f2407120f020d0207150c0507020d080d06170709020f03060f0f10090e010b030405120d18060f0b010309020319030e060304050d0f02240408 69
    0xc0b1090034640e9051650303030240c2c3c0814210750720600c0115107070700c9903030304014013040d4122140b85103945031840b00315441007c010004110940c2c414150704142954401025080305c210000340c0c40303c0c054101009101d16008100c0c0a0328101400589620351050407601440e504440c180308080c2281008209070142d429070107440e600d412800f0a40b6420003051a2030742c08032000300c0d07506907115080b6005074043c060702d450f4100306c01c1c0f01150303031403030114400c1018550113040c0247d020071900000d10b02e200c64030b1440f000303d000700506201d51200c0c2c112130360241010198092650a10f0790f9402d60311a404001584600000724040b0901861a004620103401601d40c400e80e100e8181400780c0202240c14039080c520341b900000304240e5019014245003070f500200903111881d00b0480769650903000d4a022001c225106020401640d9400080d501a40c000d000410092101481c040d1410300800d04803010b40d03100040d0b02d04400030658869180c1c05844040c070b462078071a4074099403d400362512 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 842207580 1250 842206330 842206363
    0x100503160c1406010f090b090402060f210105040609060b0906071a0c0310121104051504020c07050102060108060f1311040f14011703300109021908090a0311 69
    0x40d02c441507040010141d069603058195480c08640d0743c06214111010084501d4200244400041c054605100036180100d4103030075141c6000350241c44086520b600c0c4914451300c6200340300500c0107044c5031140001801040c0d2081040700e00303014040a440c081c00701d00da4424200015404100b0204807040d10401108044a14103803c1ca41c50b40790342c58000f2102e02c520340500d1200000c005500c002c800340010307001051090710161103001c1c40080c0500030001c480b205951006140c50343c5952004091500801010b0140d0900b014002414420103034014040c03984440180102c0049440c8000d0700700300318400e05402403030f203450420107801100700b43d075620501e804d03051a607902182d0007000d50702110301c02d8400c0c01d81c2c0312004010080840001c00c19135520510070200481d8040b070301c422407030a0120301c02c021070031081c1c1c021560f071100b60040020107401280c2c255480c1c060300c05500c0747d403025045c006a076252510400781d030780e0883e80c0040c0c01c200c030a01e4407a680309018000d0102e0042c00b0b04 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 842208830 1250 842207580 842207603
    0x608070b0d0e06090c10080c031803040f03031106151302090f06070b07090e09100b0d0c0b0703020c010504030f0308280902010206010503010219050703051c06060e100503160c 77
    0x1310042c2c0c4803406100c005009540c0540316940142c0b10b40100c0d803040708440d0181c1e055880e20001c1d002e041810800c00c5005205c10400401c111170305a0014009511035030300c040d90051882d40b01800c2c007401800d0364001c100709450080180c7c0d20300400070405000742c1c0c40141c44544030310008003031881030007411f86c01c1007001410006006c0281000c0f48034140503180d040b0103c1e07540540301c0000908490300001500900320004940b14030350401000707600c2c01070400300d00e500b43e61505100c20851740d010072250b401c0014050b0405405108114034494242405400c00d447c40d12030044410500a00504100d40d1000094102c0d20080c100e40139011100c00914441c280001d4401c01040321500507400b520402d40009421302d014000c9805070b480079942400001c105083c184c1d9980c1040fa4128280b06050007440544010b800141c0d43c0b9840020340811a540386c41c1c0041c00d1031407401015400b13100080c0d00ca003411a04003049907040301c10a14807038015695901c0441d08040c6491009102201c00c4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 842210080 1250 842208830 842208841
    0x5010e190303140112030c05030d18050d0801050312090301060f120b1f0308090d0609050106080f0f0a0b09121c05070f140a050412060f0c0203070314130815040c06030608070b0d0e06 80
    0x1142c10305181e4800c20888100dd00b0b92081580c2d50102446507036070691016820106020754038025040c2c41d207020703002040d11519010800302151483e0018041340c41e24008020500c05901c120941040403070345148140c03281a61041d0507d550343c0406000307444002003041d241d8070345044420401d43c001d10b04000399441e510340316010b04514411140d00d40320713882d84111504400b2807400011203c0d6802040103940035030b96010314050040004400740602e8203900d2800c00c01c0d8005000c0a43e003060010b04000b90400c6080403150702a0000b4200711400e81a0310b4202d40183c00c10000c0203410214a4541004020443d0039102e1030b00070a4501080f1901c01e01084581d401140311070100c17440a010718000c05004980c3d9000b0900003a002845100c80319802d13207000402082c203034056501e2040f29541300c0120600d8041100d8080600002c03900401007804102003452010b00b04514050007841d240100ca01e5a03961075000d07a0180000000d1200c003031040e194001e11140d03406005441581c50003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 842211330 1250 842210080 842210111
    0x1090c09170106091a0112110c0604110405010b090603190f11120112260d021617030907210c1203080108070b030103060905010e190303140112030c05030d 68
    0x94490407420703506100e00341110324a810321a0f100d6817010f940740c0202c4000c688441c406080e007020040c034051010050720340640b200348041442240580880c00070041420b06000407140164070614100c0800c0c0b040d02c565a40e103200701c070380002c20785101c2c80d21540b002c00804000c01e021161440d19500e420000240600600701505105d01d442020300030707aa90700d0064060000540380000c140511030041704c4000b0464020081d00d0540d156401c0c3d00b0018010010310880c1c1c012007203403007038200219400e41000040c0307100d4100b1402080c4000c3c151308141c44400e68030003090044410400800541b40d40e1200780b05030200350715800c841822500c40da2000250310844107900240d0001b1042c5e030001c51034002c0001d1aa00710b504000340c0c1031440c0c1c6591541002803110400c1241c06540703c61070302d07442c030304108038900c0359407034024000000e10780926025048822003c01e90440c00c08050040050703440384240b0500b0302e9003508100c1d00d0300300c1a14001d0b085100b00d0100b140702a03d4140c0010400c5072 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 842212580 1250 842211330 842211341
    0x303060e0910180503040b030a060f0e01170a05070909150c0e010801090209010f140c06040501061403010513020f1207060306030314030f150406080604050d08100e01090c091701 78
    0xc07100300802c2120f240c9040381d000200003400140841c2d20401041000c00020401194040e804000000e510b41d01e48040000054180d80540170000b40d03e8018060325002c410034600010342200240b80e40d100903a95641c80e91103512400805558510010081c415107203110140124224410807000c0040b02e4060040c50410102c0c900080308440049481e2740b262080351010a8161140705003817540070780031101003240044448172050f0501c080311480008015042c09a44030724000310b4900e00740780140046c00c9001e00400d100740c2c180400c1c08840600c4903442c0050030740580d100e41042c01c4400100300281900141c0f0400c5110300800060a664540d110005480c070a40d00d07400710798076007031031510340380030545815001d0b8801e100407440d1111444184003400340c01500c0440c4040d81c3e0006c003405d10000b15020755260300140d03189010781b540810301c01d82c1b12810a41007031107075061040d9a15040e1050241603080d6950314031403030b6400d00800c000710052240f0034112201c0d00050700441d000e4203 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 842213830 1250 842212580 842212603
    0x5010905160e04111c0c150e150d11040801060302090a060e0a0509010e12130e0903030f07030216030c02100305070203071b03020603042108070503130303060e09 71
    0x41c4424616001801a480c00445184140729102ca0700d550310b8a0008844507070010742c5c80701a40c2c03140c0700d0015541c40d030034580c58011403600d0304203807620721041103e40c42c0301c00c64410080210340d104141e0303580100005260303582d00b000c42d8440303c10783d15610007000980d4002c2074003000401d000400300030540202c3c00b03481c03007601c21407000d444034408403043d180c03540a28124040c6450020340d6001d80c1c0d5106640c4040c00d0400401d00070311140c0f40500344816070415110711040040c41c1040a100c0b554800010180c0104d407284610340a40c8041d02c1e80409403221500c40403038800b00310624071075016a84040744000501d01401058500a0600c500385c0604a00031500c6940038242ea42c001d2003800d200711055000345240c6000c503501d041718681110040f46204601203804405070b02c586000c4d41c0710310b10448110420344001c0d141d12445d446920b80040c204908c80041155066100703060ba5040300c0b81100301d6289800ba450f081d00607141035000448032180303042c00c005002d50001060204074 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 842215080 1250 842213830 842213833
    0x90c0c010b090f0601031e050114030606060c070b13181b2a050a0503220b030408040603090602120c03072a03050a02100c0e01091409040206030c0d0905010905 70
    0x800d200c100b803005074038040300c0c5094400e40700c500045143d4003a07004500d5100c0048000603c0714114000755040b66420f810600b5030540621809109050800080380c001c14200c0f529070030a072002d180e150742d480c00b074003602c44901c0b0003050503c0c03040d0200503007101400344041035a044a072070b031503004000d01c5d4120000c00700703019903060860014007400002741940b091a400c0c180c415201140d02c1d5401c18504402c961500c00e0b5402c45020520030f0000e00000110102d03240210303a1190340402c02c80c175485d006104500b4081007408000386c01030049508540b010305010800100d1810404000e00a041012a000d0702c1d14080051040c2604021031144019440d0090045041d01d840d00342c3c019120b0f441001c0580d07250f00403010034000e0000d0810000e0301e10489040c2409080c0c07000c280c03007000180700c003c543c0005880364250f0f0407868003000340c41c41e0b010003402102042e0000c0d03008800a00064028580000402d130515481c0c01200c10084503a41d0a21015a103403800c14020400600151900e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 842216330 1250 842215080 842215091
    0xd0609020d0f0902090f1e15010e0109060207090c2129010813050708070308031e15040b0a050d080910090e040813031e0606090b01050a030e010209090c0c01 69
    0x4070451031060350310458010b031450000d961a1549541030080151015503028108071080c500c1c01c3c0347c9001984a941d48540c029440d00d1000009014a03107030f54503444c14400c1c95401800360329170024000d02160514580820f01004280064441c100501c00d843c000e03117501d0a60502c41d01da82c1c0c000b00101a0150304480000c00e0400300011241c1c444030166000450200200d8100070000001078900350255054484066483d0170030340c0342072565441280c62150100800903a50200d0320700303080450028820311514503140d080301195604441c50740e4800d9554042c0b804050321001414000b8043c00313010007294000d141410301454000341d010603c01e5808003800c3d0581403194031140100c42c40e41c401e503503140d10390340c6d2001090f401c1004500a02c0e420b24500201081c0369032482c00a80c03804a0ba82841c840036130400034151000d40c3c01c288109802c2210202c2c450341d12034201c0d20a88003914000800195510300680607100300b0040541c0b0624550500c150710102c1001004d00c0242d80008000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 842217580 1250 842216330 842216351
    0x408030f01140604030204050a0e011e0b0102011a12390307140105160602040b072028080105070302041806210501020705010504031e1403010b0903030d0609020d 71
    0x50040e03010380303500d0b0043e02c01c1c4400c10040c20642c100e03a40281034075134003141d01800110101d003154019107900d03d80c000c3c60031081c08009554803840182017020b100034800c001e4618007100c0015212502980a801d0494114034180c0041c4605112404032401000142d00615100ca044110800902c0c0c20002d1800d0440e4181c42c00050400854503524900d403107848445005450325044040442c9200012020203000120303d440180081d03c1c00c1c0c880c071a114a201c0c2050f20000e40fa2410801c0100c40b8826441a566909040c10036130002034044c3c500c484a040c41e0502d18400c080d40019040c0d0300b01014010090341640250040d622841da0b0004140a071080140607500644910114055250400021380c0d501d98031b801e404501503030015241543c165a10380c2101c43c00c5038145e0000e410042e071a10701c034170303a4805801014042c1c5805052096042c40c0d40c00d0620041c8a59480c2c1c4030300080340040d50314140181d69021070402c0040010503034854030b10010b507208001d000c07800c1d0325001c001d08 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 842218830 1250 842217580 842217599
    0x1b08010819120e0d0803070315050d110f010314090a14030301060503010603020f120a0b0306060103090203100203040302070513090b01060c2118080c0a080d02150606120408030f01 79
    0x241180e0040302001041090900c16034810340c02d0650fa40d080340c1440000c20108801c0001580134030342c035680000e080c0d0741e03410030550740e4140c0c2c0c5c00c21441a00c0e58000c0c0c801241c00c280300549960800c80318810803c50500040e0010005245000415071484080100011001c9030743d015490040d24618030200100c00021b440c0c0c4802d004071008104244014000300c0d01c80c0c2c1c0038011000c2c001e8885480c0100c0712114403182c1204a45c0004216190401040141824000d080d000a030a0805000301c861a40c0060b446c0c1c2511050441d040d903011000800b41882040554014980540014041c00c0041c61201c09828400403d13607141007000b0000501c3c900c01c01030031103510340080a0611000340c0640c0040040c24034803c41c42040310003040080c910323005600c0701004040100040480415490910030036420541c410001c035040f90a1600c00d00fa0013260705d81d6943d040300500002e5640b0000051054042c03241c90403201803c0d10100405c03c0203580c02107004074808000c4190070382c2d0322008103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 842220080 1250 842218830 842218873
    0x2040f061a03060310020d02090102010e2d1006060c030905090606070b07030b090a021309060f0b030403090801090803040201031508100e0a3912080a02011b080108 72
    0x701c100c898008081e11001a07210003039608094002c00769411040c010a000003a0b0700031020726220309a000480300d04545e024440c684c4294424006000d2702580107110300c004a011503d03126050790b4442201c0c81001c0280270f40014074015000400a00da12842c4c000d295000c0940200d010900201d0f001c0b90a2401040c81d502c9880020125460481e241e602d281d9031080c094065028191a6550b110480d651100d50911550710346000589861052012040b40042a0700c40b00343c40385071131401d120400014180e6010f848446c52844c5e0b0b80c0e21249002c07242040d0030f5201c84070a51030620380700c0c02c000f2070310300660003107000340c2c2c003030103802c0101151168003041446140007691004202550f2060250442c1e4540b001c4c0100f5282d090700c02c0d40b6141c0800c1400310760132009401c007191002d0314025161010070501d40307034404c0b07102450609000c8401c0340010ba20150001e072003c905904654401d41211560341e2a040480021014000b0b001e003101c0c20a00584489000b000e1030401d2080c0d17143c81b42c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 842221330 1250 842220080 842220089
    0x30212150c0f070c03080a02120306101b0611030a06051e0f2205010602010c0f091404060b0c0c0a091509111605030406090906030506070f21060302040f06 68
    0x80840d1501c4500da405040d500010411901c803509000394004a1455490640198059885c556032103080c0f2900078241501d10504240d9183c0030b005000039a222106054080c1d605810840010210003145041020300c16a0041c103d5013000c4201002c158010701550003010003040c1401010340314010403840d200c00a803481d0344007219000035a011315240d00e20b001500c81c05410103a0000c120300c1c900841c0c40c5142030381d8044540725401040030700e909208104000b43c55282c00c0240c5441e08a008041884030f100f40c01050b0080c200d241e85503a80d0303900c0070000340826400981e403080444c103116241d60802d00864401e200510b0005034410550003030713070802402d620075041e42a040088000040820a5a0042c11036040c80300c4501840311400c0d044100380034200440d201d80c80c0440040158005400076401141005030400018100060781238000c0480e091070807400ca2080d000703c4403000c007030000300c001500c508000c1c1c2c00000076a02c0b880689009980a11441c95030f00018010388070b45218 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 842222580 1250 842221330 842221363
    0x903140327030d0c0c050c130b0a1d0a090b040f0507122604050f060c01022a011b050708030a24030201080f04050304060c030c0c0f0e07080405030a0f0203090303040609030212 77
    0x801d40b07048d1800c1031400c80d202081030400146034206001151030741d01d20b50014101440304044d8268a200111151540241c01c0f0400b40080d101d6075a81404482020300010000e54040038070030100034092240f440900481d10881c05180031a013407102d110300300c42010311201002036441c0b12400c90440111016150040c018950002c801c9042c4907081e88220500c0400b95801c2c0042001468101c4400102c811000300084420b8000d03c280b508542e4500c2d07c91555000000382d04146940002c2503444154001d9501c40e12503031303410048000b5012000409851040c100a415182031410746004180c900030703a5031500300c0d543c03080c0d0f50000c100309860140956005010402c80140320b00c0400700b00b24805d24103440444000e40e0f920315a13071070503040305180c0c020010b401d0002ca0480a042c5074022606e1034030401c0c0c2d043c80d4803204c3c1c0760b1040c41c0000d0100100f8030300700b0004038000c00460304082000303030031a42e0b29659000000c1020586020803481084000491000341400180c501003c0d10240c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 842223830 1250 842222580 842222593
    0x120f14121b03120a0501051c02010c0201030f0e0a0309170c06040b0705070f080a060b010234050d0b06010207050303071718041404030806040903140327030d0c0c05 72
    0x20900081e4006000004101d100400072040b151281140c0907000300d070003060100c4e5a50400c3c04004881e40070840000c00044050103020240c1c0e48503100c480d4607030302030800090143c4101420700c06412164201c2100344540d942e80300070035520244a10803180c01c0000460361000102c120740c2c07203035a160b0b102c0390701182c1848140903060030040240882c611810444411039900e5840109a064a92000c40e594004542d03000c1404040e006a0f00d661030b09101500381519290001c158642c501c00400517090f00310b01100314101c2548134103801070f007801003014162035428600b40030a9801251910b0040c040c255000641d810000300751a9016841558134003440100008041c2da60401c181c050022072040e031520802d03885910407849800e50119489810f49042d0401402c070f400e01815040c0640c1ca455003180100e0362085a03004014512449070781e59443c0d280c502c52000048102901708116410020816124000000c1000c914121414488081c00150a403201010844090440e40248 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 842225080 1250 842223830 842223847
    0xa030803090106080a0f05280b0402030f011d0c24030903040306020f0c1e15270f0c01082e09060b09090112050322120f1412 55
    0x21000e19484045400009400742e510044586461303901082900c10010110102080c000c0a200003401d458075080806c140640c04603d020f01c038484c41c4400340c041940c0402203400c40d64240024064001a10003c0c052a06000705181c4950340c089540344851240303204402c040d080200c030801d01d4024020845407000340491201010364001096941140020800400002c28034402b41c00b5800823040010b4403400000180d03481d00940384c449075510b0480503200d52002000040351207120380c00313516035a0b4070b460b00c182061510441040e4038a2055070b81248a016503000240340c1720180c00b0200b110b040c81c20020041d16000030070f0b180f035407101c007840003c0c8410202c2c001286440c04030320811040115601d910150886041d0340007804007207000a0048450711b0801c2c02c1070b0152807004541902e0f04250303514140d5a114a040030b280e074103080c00c0608003a00480e44135070028200b03030403501120703081880c000908034030300c5200301c851004a61150051480c0065640c1c070280b0b5060301d4602d4801c04 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 842226330 1250 842225080 842225093
    0x60203030610090b070b180f030a030b040603170a080106030b090a0902130c03020a0f1806200609010209040516021e1204290a0203030604020f16030c0c05010c020a03 73
    0x40740c1c1c0e5001449400a80001c4c0400c8800082c240d19000d648605020b00305083c9868428881c1c040001d01035029280310504a8004800c50b40070b200c4034240041c05000803408500074128070342c405000130b501190301c800e400103c440102100002583d035120a03a8a0308401d03011030f150310b0b148540158940c00092201002580410301550000302a0800c00d110345000704c00340c44100d03500f100040e0300403071118040c5801200311524501c0508102410203c500c0200750714542c1c61140300f081000c0d020081c0c04814284040d01d98904221055a41c64070b00012101d010b0360011924901441c5031030300040c40401480d51807142d20555901814104a452007144028080840c0024081c0181003001900780300e40801030005140c956402403210283c0d0b800384031810f84086443c0b174590b104002420555a011045135840700c411100141c82e0740f070340310384103846014160400c3c810596100550b000e054200c00c02103041445170214003000c6440b08011250308180150082d0400b01e004805d0001030007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 842227580 1250 842226330 842226349
    0x3290906060c0a1208101215090203030c0f060709030b180309030729030c04170a0606080102030f090712080318010507050c0d0801060e011b020a0b12060a0602030306 73
    0x900821440c00c16103020038080c10f100c401c150840d00320100e00300e200001a0460951644480d990301c1c003034000d9140050300e14042c4902c8070000d21840e98802c0c0c00a14103416444404200e8000d81200c1d2a9045000415030340c402060301900c240c8282c00000d20500d1090b50442c080d25400342981081e6201e070880514448040200b8090501003413180e10403e440402a000040190f40349001999803003400c1c01c0002c64041992000540b42002000f2001c8040d00482d000c96005225001d076400b10010080c0c10130090400061415040100000c1c5a1105401031800782030200c6599107151100007040365900980d104600340070035900c903010f011410b0701e005176901812160180d0000415040f101e4219803046804030007140010800c1d50083e0010042403040040c9410801060350400e400600304010026803c0d042209140102e40004040e0f02100c15042d0701500d9900e0b00ca48805021041d03400500c2003440600044d000124245080800c0d0012104650041c62851301d41d501801180761 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 842228830 1250 842227580 842227591
    0x300c0a05090a18150b0a1b082701021b011b02010e0402040b0c0f01060e010e0a020c011b03150b0403081b0709230403201005090d032909 60
    0x801c007000000b942208420840c0921040080009400344052130001d42c2001c540c000389210041880042a10781c1c0043c000034412192400381e09808032540b40c400d40a11412000441141c1007110691206000c81c80d0380c40180d200f40c00b40c91344544682a907040318000d46140ca40054891004000d14003074018440c125540103140c106c60480c1b03104081030990340071350f2220141200001c1d15154020051085a1110319030a009105032880e2000880007520306020380c1180f100c0c03c20102d20402c00030f0381203c40000001e0002c3c401b141040c00107040000c0b00f0b0343c5020200381844c03d004031500760841c6c0380d82a109210310396410300781561100074280e004005d000305045905c1200105215040142d140140540c42007c100d01c84138016540703140580300d00c01d055070b20320b01080c00002600049070802c2032010000d1020301c000c2e5000c0c09460041403034800800c0524001c203100b0159000b0503402c1d410744542d1000d02c2034640589080c450040004250000005800c640b504503140000440d07030081c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 842230080 1250 842228830 842228839
    0x1d0c0f0904021902150103080d0c122307110303010b07020a031a150405010321050405120a05010e031e1303020901170708060105060f1e300c0a0509 65
    0x380400020408a902c107481c202c40c12411120080d00580c0d040041d40441e820422000c1d616514594603030000340a030584040c0007580300c40359480014400d100c000030741d0001c90005e0021511210400c079080c1d101340101c921440c4407a0000301054021004101202c46800045156a00c0c2110f6107483e034106010403a4400e425180000100b0004640d20b00380b44c0e011a43c8032003c3c1400081c4d9664030302e400071001c0c010341c2410010408035081d034081000c101843c241c9101480c91150081301c081c442d582080741d0010034485820f00c808000103138240b0003881200200301101d07000156959074021a6441007081c0c3c0080d200913650714803500a04a140300d42d0320aa0100c2d5101e60005513a1102600300407224010f01c1040840d1060800c480c1e07004042d09006840784c2d504010115000340b0441400b20003030080020345843c0410002c00181c80e1074510100241c4401038404159400c0001200c0d4481ca2030341d02c600c4510092540c20f4041c040e00e000701506160182d03d200a442d660004008290f01 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 842231330 1250 842230080 842230087
    0x100902030c150c01050112030f05030703151418011203051620130905030405150403020303031503070e090319030b040603030e040608160b160f050c01091d0c0f 70
    0x2941c0b51104071000c0070b003030031403116110342c04111064216103050b44441c0c0300c13401d0741c490400840e40000c0d01904020107854180c2d92661000343c1900642000000e4006040d0003c40003e4480d150b0103c0031044c10f02103e68030095441d004900d000006c0038002c2140c0a41002d5040740000e00460080c01c881e08184403c0683c1d6805031103a030300185101202c421a524500b403200102d16000c1041c0d000c00100900400c103c12240d110a41e4038001c60144d64000c442080b40024180300c0d080580703005550041c116070743c2e80b42601e64040c1c0721000310340c0305020f8400c00c2808140c466214100d85d1285020343c1c021410180ca9500415680c2000002281071503910183e04101d0340b500c0c003d41300614083d4550a030100514400d2004460a60b072042d143d5401c5609411000d0020341c0d16501111001840e00b5100c8182c10000e01d403070f0f20b500100808400d0b64480900c10040c020515610440090701e59404803035480c208440f8034441840610802c585c03d000142c805507042d8080c0c249500c078868003504 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 842232580 1250 842231330 842231353
    0x30e12040608010e0a05071d010c150f06081b130608010c090302190f09090302030c1b1306030b0a1d1203041203020726160b06150a0210090203 63
    0x160344560030041c0003401081c014028421032a00140e00000d0390381081045151002005021440611007807814215086007020070344e1241e145070f854141c010386c0c80012a1500c14001000b040782206131104a801c042c0002000c403804101c8041804003100c003990065640300801c00341c046800d214407006c0f540c80f9800302c1c48010900c00c06545154175160b103045142540100040c5200c0c224040306007184451040c4102884900f0481c2118900c10001c00d00741c1040c0b50581c00d5020f524450b12192240d00b1941340840f42e2607082003c5283e042d100442c1203034500c2240d4043d070744d06000140040d8205008101461103a074480b103820013030302030220000d00a040d581420640940107260480b0008030500060045c10690100c0ac000c0b1030400b14548441aa540030500e410a40c01d02800c3c12100407200c090031101003150440b05400c40808491521440e002d0061001038a03204d00030300310052043c0301890481c0496031503d149030010040e500500d100c0901400110000f07c0c0c16001d407840400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 842233830 1250 842232580 842232613
    0xc030106301502031e0106090e180607080a0609020301050627130f1407080115030f36030509040c030605100c021e1e0301240812030f07030e 62
    0x20000701000d00302503035070b0070081c0c14000320017602d16005107646000801004840d0308400b544044603903202201190f0781d942e002e1105805d03081503005016000d42020042081da010407024030820a060040080e16110407142d4201d02003402004c0d00101c04000241040ca0310000d2502800314580d65072000b4890400421045005100e04081c0e8039283c1104000c100d410f0300940070602e06a840103a042c0c60610001840c041044c815044240c640303000c440360b4180700e1341090b110607624460602005a185213041e905000d42406552032501c541e042a0514800c0181c00031200e4240d075605042007840c80030480188480518442030507a160000107454507100ba1103440b1401035103448481d49128014082415400601103203420480070421810307540303c41da640b8124014a01c6040c035120400c000c42d006040c003c2006801141108803d105041920011000c0d10351020584484c44110b90b07424580740000c1d100d6006114083c0006070b0b03c244030354001c401c1001c8050803510300c42c04000305035 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 842235080 1250 842233830 842233853
    0x1120e0706111009110f0d0206160c030b151002030903100f06091113120b040303050411031522020102030904051e04050309012a02090912040e090c03010630 69
    0x2c40d141300b00e85c50603445038906a001d4206201080d1403202c02e4000c2540090310a11605c10114041c0c19803880784001d01040e405c1e4400510f60140300c4920a08144a441c1004c00c000c0c40c1c1c041c40341c003005401d4a00e880c404070548061000240080c0f00740c2c080c07070240708040d0501d044c0d850007036075640c00002041400c50042400c2c0361201094281e0301e50302c1e0300442289811541100b26800c1d5003d005800060b4165421940182c141c070b4005010340780c0745046501030030062003680c3c0c18400d1030341400c0d10300c640745a0070340507504e100183e280d01c1c80e81010f082420405814080d001d60801e0013018101e0a090300020740c0490705800d40151001c2a41d035015000400365015101e641c03020036000e01d55600804400202d1522840340bc45800d100007420789100000c11009020b142c105011078140001000300118105039013801545448e101c520361104002c0441e0b0207851446400010001e074103040c4141c0d070955206c5051b106c0380030003942101d5000014510420035441c090900c103c04038503030401d41d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 842236330 1250 842235080 842235083
    0x70f020d15111c0c0207030803101d0702060a0b01050403060207050c042c0106140402090f09070f02070e04020102072105070e0718052209081801120e0706111009 71
    0x307064480c82d160f041080d280311164500348800d40b410a4804080750000b0700c40c022668000b00c0159a60794032a0049407c16003a0b2010050240404100f83c00c0820010003900c81c06990742254495590390b07001409030f0300030aa0240c0030a40c2000305201145d080d80040140900401c02c40c0e6114495074042803c544103110443c01000000b0701004005088124a07461041c0010007807041d2410702401110654110018520a03540058070460503100d44001070740d2003000802051641c60103a002400300401c0280500050142c1d1402185036000c0d010101c1c05250107074000c00e8401d0400340030b5014200c2001e021314038042ca15845c0c41c0060401c201e00350103020134260841681c1020302e0041d0013100712040514034841880c0f014001070702c03403100d0101d04200c500300700c0007e074031203040304002091924000b03020403500140c08804410001c140b142c1e46682030380c0d03252100314580320315401c6071a114807105090f00000d40c100300041c403911b000616040728406542ca600890404242110030741d510 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 842237580 1250 842236330 842236361
    0x31506110609060106120c110717010b06190c0c0b030103080703030b0607020d060c0e060309061501020607022d060a0f05011e05040f110705031e070f020d15 69
    0x1030520528006106039070700258280300820b81da50400c40003030000d00580c04607803e42540c0c3c3c000000d94521804131142403480030010341c0d0209484904020706d40d4400c2072010307965820440c020301141800c0c1e045844011002c1009007810340040412115419115000d50f1561002000450f203a29501c00960003140b00d801c00d40d035503101c00e1a01a00703541e118041d19125542c1440800c02607181e2500170b1084940c04140001c010200c000150f03a190704009809401c40030100402213508400500c490040e0300d05652402a010f100c001241e440c03104a031240016000070020440f80300011030707410382c1d04c130008800c4028801d00c1c680c107070300d810000c0382d45c600c0d00d9884400380140d01d00d80344515805003c4560066000e65181c8620072001442846043d000355a140320030100c1601d03a07423202011030615030069603981c00c142096540c1e07400c41c04040e107104400c01e211031003081c21103080301d4102da40003048c42c0215400d9001c10800300c0c1c1038541030760700fa14640340c1403c010034188030300c81d0500d038183c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 842238830 1250 842237580 842237597
    0x303040e09060709210c081f0f0204060903110411030c1b032a0703050d021f06030b060d030e060c0f0705040504230309040204091e05071e031506 64
    0x100580d00d000c201402c10400d00050030b0b000d05c5071070700404200c60380140c400840342040c501e924150305880035692102d10f1a01407040400500303003c8000181c00c0d0600d00d4424025401036500b004120b220350f100e20300c00b01c3e07291a03040001a002e800e90b0380001e00b004100040341032241e00760000310b520031244510818400520b459140f03451400b04405400900d0055040042004050300c48488240001c2300440b40f120308140c0380581040f0740b1000c2c40d0f1000c2075a00564011902a59883d0220030030074044030140b0074009025054412103045981107401c2c0541d540342d16080c0074903840080405e42c100883e2080c1990301c4d440709030007441c8220020000f40385400b6240b24481c1450720f40d4115600c198141020722000c074920a4094560a1055041c40c44801d004170002d172451159405440d0054000f0800084000e00e591000300c144a400354000c9104500c20103003821500d0889110340850001c206400c4029812480090229540c0c2000102d468400c900c00c0c00c4140b00b64032800025908c403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 842240080 1250 842238830 842238841
    0x90c0306031b1507110d080c1b0d1104020909010e06040e010b0f331306021f020306040b060c030703021c0206010501141902010c0e061201090207110303040e 69
    0x10000c0902542c4500b11864001c2e8040c0002141d110b118240c880401402052210500c280903581d40d211010003407100708018074a2400030540d411101c00715440b40250460070320010810030306000c01e14801008a24000000d544944a4001c44e094a0741c020340d0900001850351600d2502502806907920555210300c6c16404000c20741c0d003500100d840340d0341000c011000076214141700b44264402118014800700341d400300483c09042c1241c00e8170002414a0424144000220042212500b400c008103815a00d031401640d96190032482d06015120389100008104600d901851b04100003e0012440e400c280000503a02d80100d03007003d0064200041c59001c05404100c1d8400703001183c5981c6045101c81c007030194407440148a200d060280c0350f198040780182c400200c617200e00844a40340344800680400a0081640005020105502c0310070242a40b0340882600c0740c1e604148113003a0301ea0f007400c0c00440650050041192130014000440504e030313405202400203032103844220724030b92500c03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 842241330 1250 842240080 842240083
    0x305251203023003060907030e03070305070302010614060316030f0f0218010e0307121a07110607050f0f0903030f120717010f050d020a080f0d110705090115030b090c030603 76
    0x50200002070b003083d55880c01d40d21075a4401d490744038038110b03008480d96440b100141c01811050899121074000059110101a00700001c1c0005134003d42c0200100c41d103400010700079250851180d648020180006490080802103015000c443e502d004a00e150030808100262001c4e8004c0040a42e00812000c0900101c16282e4040303880920b000500c5070742d9040426290030450003400403010035a0580e40900201c043d0740345079001040d0500c501c515286100070400da9032400380042c0340c011030340403584162080c0306440f1680000407090341b50400c807981e0030300d07140d01142c04241c1502080c4040c000c0b41c020603014040e508001c1c030807d5214a400c901c01801c0e1091907000b00741d285540c0d0300501c4016103400c6400f09648041e28070080041140c00000c0314034156600c41002c900c6441655443c0d030001181d0134803007140030780303a09040b09581c200103a101c4056020b0303503810409010040124045c6400c8195488846090002d0249207070008507440076130403910b841c000f1100100717115035401d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 842242580 1250 842241330 842241373
    0xc020f030702010f0804081c0504210905010f17010b030f18060705030c0d0e100b0102011a0603071e0801030c170604020f0612130b010f030525120302 66
    0x1000095441c008980e400603003400d2040080350b00b0451070500180821009104891a64074400e030f0701080408410301030300180804440c12181141c910070104201c680001e0780c04101c5d02d01e0f4560400d41170030a8011189003444602c0d000404c148510720340c0d182c15006510502a00d584511340c0c0e600e2401c4c100c41a0f40c07050141c002c2100070300c158014a9109008030ba4103811101c0c91811580c1d0352a8243d03c240d19010740d003505a115841e02c0500040101e00207403440070207100c444180012a80398005908841541c10521020025112410014a4001c001f168804101d041812500d00c14103107000c1410100711036107006c5019400103205000340c3c092903070028911643c0a840040303c03018001c0d19200e010300001c0c05214415012110b030b60340e180c240c4205481001621440e40f4102d80036500c9003549031410f03101085002c0000c150b40da031403224501504e401000a004d980d204800c2802d050348600100b100d104941c8202154021b45054a5002c140c0281c3c0103003200c01c20498803042410 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 842243830 1250 842242580 842242603
    0xc030f0c01060807080a0b070e060415020a02090a090515130503070c03031e020334050c09130206041809020a0303180b160809060904060e0411030607080406020903011508010c02 78
    0x900c80900c4000103100c1500c156800302c01e0b8588074027100014130215020703008680108145190724028141d081d680002c40b4000c00d802120380c013485448046035881214904c07240a02107030050103040d038005842d10300898010840c076000900211b072070380707955066421405080760b038a00812030400c1419400544500304c8103c0395000d00d0004032004002c0d582c2e11941302856111401d10304034101d8007042e845107401c001d40384a0380d142c1c4031100385801519029100891481900c2c0c6d9408030304162080c0543d50302c040d5014002519041c207040c0d81481180c89482e11441454031a500c800061b252005d0700e1000f14402d4568003801201d000d003520048441c1d0f00910342c100e800380010599501c26803040c20001e071700007441c41c1d41c03092080041403580c40f400007400d401c80d051040009105040614041c45a40100c1c1c070101c079590b25800301b5445500c150f40300c07000124486c011401103207155005000f403c5000b4000200003021482c007480320b02003a0301005051f551901c40b802019014011201d149 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 842245080 1250 842243830 842243833
    0xf020d020d050a20010f1d0301020f131505160c030f03030507020c2e050c0304120c0905091e0c030a150f1407111002040909111c080c030f0c0106080708 67
    0x6144000000d00b405801c100401c1080741105143d80c0d0000781e01f0032540d1260300580250364540d5410981000303070b40002c4141075a00b03010600000c8859a910350400d0404080d0340b00c038a811615030000c80700c16002d0310300380e681c86001100000090b14004030701541c00e00c42c0c2c0b4003088500e00000007904000164031140c2c06100c4442d1240d002840d403a1590161003d240350480d0a41010034086070315018808200362644400100418011100e450481c406803042030041ca0294079640307221f050b10800d40c0c42020990103050450100c121a4140202c0361a030302d0111a07116840c040003c0c6050161031003900e40c07203400032915948080c0c0f4040d414059a0102042c001c0200031076500c203104200900c848108001c481445400420a21195540e2f410b4004190344894a030320b103c2d0000c0c50020011034600350300c100d0122185c14411a880d000c0e10300461014416030448d00c50300301642c050042a10303140010007040400f00305203006071215500f2500005440c3e41440b102c24909020790704411030307a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 842246330 1250 842245080 842245133
    0x1009030905010e15161b080f031c0f020d0f050106030e0d0c0602071e0c0501030f0513020d081908040c050102010b060f0c01150e19050907030f020d020d050a 69
    0x32901d40403c601250414403001c1a91803a40c3d0540c01107003207040400030700c503011440403100c44218900303111007550110410b44522412007232019990f885400c6075213102452070344100e028a001d079404046000000d040c094540818821040c0c00c6501e4502081c1720580c4c0e850050058552500c42d5085404189000707114400311014007820031075401800808207a00020f05500300400c01001c0b1044031030307594224004081c02e1821804041250149500007071a100c02d04010400074021076018405001440b620303006180c00340320580c13001c2c0c4e02c1035803840e03410003540d44180e0415400081e19280b40e9600c00c0503051902d0803a000101d04d82c00315045a040090260301d596941e001c8400d0011400a801d81d107400c2200524090003000c0154070b010310602c40d0004644003001c95452250702d0154140c61101c005094010840f003060b1140506e40e80081800c0c0001014807995140c1030b8002880143c000843c0d900090f800380789080101c60642084c01c41d80100540716141c080702040384502e01d0007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 842247580 1250 842246330 842246357
    0x607260f0f070602041d0a150f0509130b0c040515070519050a0501050106120b030d0915020f0f0a0b0f0c18061e090a08030313140f100903090501 64
    0x369030069421203200c010001419034100000d5a04660040c40010790016030034009001240c4561300880d0494409414055240b07100d8140e81040003c0c2e501c4801140203083c01d045c24003c001c00c00600300c2c0c01e0710f140050003c01042884d1800341c070801903411825607403030811042c0070b03002020310302e03141303d80d4010b1020000040300403c508900950445046d41608503a0811a00c2d007038221101801c25403820001290442d03002c20f0800140523030090900c1105a24810316603940e501e91000c00c00545511014000440500d052071824000d43c411103c201804400c140d080400d500c0b50003190f40e000c0080303a410090f501c0181c1d40c3c08682041007803458500310b0711600305480f40750107107010411203058500c00b558941040e9a09000c240c2d0b207048260400c8280c18500b940710708000c61003001010380020b00c503840001120b10403a0000d0303000344074001c1a44c40d455910707038090715600b0500590030082c0180000304a001004e08000070007040502e61400c0c0600310f16642d420142c104804060a484c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 842248830 1250 842247580 842247607
    0x80c180108070e130f06150b07020901060807020a0b10080d05030c070f17120901060b160821040318120302030a08101e0f050303030f070c02030309060726 68
    0x2e0807075040340362103072059540300d1040d0803a44011200414203980c01c05403a0521140b54480181c000300ea0542c00d0459032031b20b80014030703409903000095000807910010f0020301e2013100a590440305600480d801715100e42c1e601d010980342100d1503895600c54540800c49844208a079445000c0542415865402c0180c05950346125000010b0400c00300090f05104101d114400d0400c1007401302c3c0095112946032244062103501920f58640c0d0350b080000100f05402010b00300e5604040102c1c082144d00072039a070381e0300b243e003201407000280f900e110a1000000c0101000500c100d100f5641c40c8001d452400c19112804069040f01062030400082c05001903000401c07920751582c1410820400c0d9500d00c003101103444145c00a0030107032414201034454149520342d14059488800103010030700d807100d061558900003241d444c042188d00101051199000d0280c5041d154005001e4a103021500e1011641720750010308215011030f030041e1075900580c1031000e490f07185001550341e20700d820b50000d00380 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 842250080 1250 842248830 842248843
    0x101d010804020a06140f03011806061d042307111005040c0b0d0b060a03060503011107030504170f0105040c06031508060c090307051c1704030c03120513080c180108 72
    0x744d00740541e01c00c080351249003040c15900a0f440103007915599607110340f00c1c800c0400940c00c4d088040d506100010903044d00445001410700400d50740414800b074448100805080d0750401c0c01060781c4582905101c0d14400c00d0820f1051405031942503421921680c01441c000c034020051103002d1410043c000000d034451070800845030104002d9407a503448095a200402c0680c1040358803c00000d424060300c0c1e00764018000710380b800c40c0200100003400c0c1d207080552107095001000074004001c1031203095405042c004002c0b1100d011280c920006c4000142190402e840c00c1d03443c11994030041008503454050780c0d1040858900240506203820401551150090986010500e020a43e440b242c0c4003004220001d080c01441c0c0b43d4041c61000f03400f4141c44100c00c095401d00c24100110008103060703c1140c0c04c4035071000754801000d10b10b44a2000034295540300008001040100d503e0300c071106944003025142d81d40150480910103c1000842010145207500010000004001d034100102d5003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 842251330 1250 842250080 842250089
    0x190c0804060e19050c0406140f0607050a051f0b1c111206040c06082802030c070602030a0f0b01111905030f04080705040b0103020705031c0209101d010804020a 70
    0x204804a2060b0100c2c00d21000d101650201d2889a2242c42030240000d61420094001d07902003103119107680d8030868240100c00030760303044544244030f07034154140400100700c290b0091068a4006241d0394a060078241220094003484082020340d40381c1c104c1c148500d0171180f00858100c060110914a50b800103a5910009030112202d255503078071540b10b524043d941c1083d00400c0d02c506d4580391070700c003004002c540a2200052000030001c2c0c01180e2a1040c80c440d00c072801d0742102c85a0040340c62a0196100521000c503041c014450b1400040c21070001e5801003120030800f050402580006404076424024098100148040312141640d00824503001150f41c1c031094104030403607030502030720b10310400700c0340421003400180c009031005020884400b66101200e0074800c143c21200110140e010325000580340350010045501c0343d0411409409003090121409030802484000050074000c608001c0d00125900c450000c0341a5844402c000d80a5000d0922442c0350400740c012410b01d4000380034 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 842252580 1250 842251330 842251343
    0x50702030c06160b0c0d23070306051f0203161a062715060a17010f0b0316090b18010e040501080a0f14030d1b0320070c08060906190c0804 61
    0x8504845e05010842c0c1541c0707070090090282c1d541400442d42d01c49030032001074030049840f6001c107581c58440e000f480c0480384001c080d046444884d08840c2465022070340c01405600c410841c9a06501c2c0c0302201c609918052001c42d00d60303981214840074103000007401c80c1d1042400c441c4000307040b161083c820100002090020100d07a49502c0e030700d203220164400300d80e80002c001c1403141c00a503029214090046400020812999a07034034002e00b14642030260640782c6c601403000440c810507694003295008103920740310407040e503503051445640d07101c544400403410304811603070072558200406103003400041d01d00300210761412402d10303141c2c40040b00050484c120380c4142820303c070b0540b2030001d1250b41402540e80c0c8015144060b0001c3c2140300300034100b0300b0030303141480120317001c3d2003104030324014a080f4095031b41c58010941c005603c05c0b0400c40d11040c1e40540071070721960402082d48191800b000404843c144981c2c0070401c201910f4410700554200a12806916800105103410551111 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 842253830 1250 842252580 842252603
    0x20d1e020106031505100b030c120916090510050901140907050f040f0302011205100311010507060608030a030b0a150f110a05013e0c0715050702030c0616 68
    0x5804902408081c0c1c8043d0101d401850742c040e00c180d1a0f448580603500c080c8008400035594000541c040c00201c60070140003205011101c0c014401c1c0301d80d9076102e4a0001590000c1205002c1c96100314080d070480d00c0c549940c0d600300071100c491098280050306084500703041661600174134038040003280c40078a0061280e140400d08450151040e2000015001201900c81e17071201441c0e1044200340c071085c0c1c0025110b04d03508510318514841d981c043e11815124120301d9003580c45a807501c41d41600d096040040030454040400c6240c03290304040e26111001d03581e14080020000c080c0c50890a9103485501d04000410100d00040103c0e0601035442c10715840050034103d09481001074400c81c8001030007000584410000c040d40001d400e18810940c092020b03d0301d1420021a80c0702c10403450322500710741c0001c0c1032003c0200280400d604110104d5040c25191001013494442c000f9203800483c0022511404601d004d01407100b0402083c0c55550810480040b600c02000d02842c01516505845 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 842255080 1250 842253830 842253887
    0x405180610020a082a190318030b060915030f01060e180d14040f1205010c030204050f01362c0f100302060a02030406081f06050f25060c020d 62
    0x200807142030b045c0e003402541c00c3c10102100c50f070794507000a40e00728001148440d810401c480250f044800380c1c0d4010030320310b52654445080c0f160807240a4107126110007001030300c4019a9040104050780f128400000c100c0c2441c040140a4105000c1c29076808080e0341c0c00030540307121001500e084014800e14090380d4900b410344500c02548a9038110100d840c1d01d4400104c2c032407250704281c048140c450002080031b0300700d805081f0128012806025442040405080319562141010b60040881a035800d04140f50840c14241400ba440001c401344408145003041000c0580c25a001c801d00351045000c02040041071000701d941c4000c2490711101e922101281545d00c089400c07001039580504142d690300c4550101079070326000b52045000184511300020f4580099584030280d080e0040c50324a911803d04205942c00d400c4420904941d9a050119000e00006815046100c107862155010400c100f03040c1501510510001c001c00d5521104480d1b500961180c1c41c402c64943c1c030a58040d148501 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 842256330 1250 842255080 842255137
    0x3302181e0a03030302040e07032901020304090504291905070203090901230a0506030a2a0e1e0a14010c0501020c010c1b03020705150405180610020a08 66
    0x1041110760421080100481019096802801a0f03400290a13040c25138034408200e0030780d9407400403070404070302c1940d03c0c5010042600c0940340500050060300d040540387c4031664111603003200c040d980b0140b01c1018a1119402502880840e062410410214501008001c1613802580199103050b603580c80001c44013403090080e6070100c031340200300c10050b5a480124080c040c07862403540402070a5103a01c41c1c1c0c1403501090013400c40303002a207a5810766448000d000010300048061a1748407004502e01c1c4103002c0b041e01400e00380c0c1c407180c456154035240c4c5000c0c006031400c0e030300d0002d20261005400350303015a19101a0741c1114010115003122200c43c800480340100d2040e0024525070010450340c6114806412040840c0c000d03a03900040d4a0002c0802d0304141030082005d000350300140300901642c14008070390190410007407561403400d503540010402c000380560040140340401020300c21a4507005508003c101194402402056074588079071041d8800e0f45090800c140c0e040450328034444e00d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 842257580 1250 842256330 842256379
    0x1903060b0d0e010506060c1002090f030d111504050a12050c0d0207030b0c070c12020414191b050a0e0a030f05060901060e150418330218 60
    0x860310115181c007a40c4000101074660355031212041e508020000d429800c00005881e84400c0b070300300130641509982c07240700096005801c980d800c480411803042c0180c90401c00b9548120050b078449000d441c0440e046d40c1045109021400343c41d00315428400801d1000510303480d19070304103a40e4100e19100210950303691103003587e07055242c09400020010550045095400c5038024000c070340c030603a14241c07000c000d0300c2031040040c2403205c0c1d04010710a60300300000c2407462a10141c0f0020312800352a510844140040b0f0781c090000031a40d60b1007255840314050b0f024521010018600d1020660002400a003e01c801941c100141e80354013a6240c0e0b03409800200458000c045c0c0e982601e0303e03080480d12508200c444242c00d46c00c0c10000100d2550b0018010300c180441340d00301411101e000100f2000d0514000308813510510010890302007514415203000c500c40404107081c211004e0400c0a040781e03131081c94441a00c0c81402103403160100c000d01007180b81002c1b14082e002150f01d0030600b4501c034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 842258830 1250 842257580 842257589
    0xb0f0411040302030c0907080f130b1501110d0203191b050a14071a0d090b0903180108090a0204110c1906050906090d03050c1210050f09010605190306 66
    0xe040c1004003488160903002041528000d03001c0d07170300d04d035001403c1c0090550187c03a0400010b1859002130200702c04054980e4001c902051040404a4a500c0d03a0040308010707103401040d242003054941b88c540c1c100756001c001c002d0749006003a1509c059400a51030740640d07840c0c60351908103404480c04041c4541554003461201c40192040304440381461036403801d2414017200c60380d00710b100d50004828001540070132107000f880d080306010311000d5010001d0b0004403041c22001d031200c1d022000030362001c09140c4100d002000868480c0004038200c018007803114106814000640140b0014000104802c01c140b90103643c0824007117203031006aa40e501c15840e118031140903141c0369181c2e14500d0000c100740305006000502460300c980d0708681c0c5510041e1350082c650703400f0108140c0058020781146a01c10540b625072420061000309540040390100c4964032000180c44e002e000b585003e40003002c03015001d440d110890360520300c0203409403040304070715100c540c8084007841e61030740b03c0e421000c040c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 842260080 1250 842258830 842258839
    0xd0212090d05010f0e0c0d0b011221020a0209060a26120d1a1509151303030903020a0906060206130501021e1b0d020c010e0414010b030901050a0606050d0b0f 69
    0x461103001600c000d18178141200035034080d4507406001454050b1100050b00e81000c1c2c5d44245918001503081ca8032001d0404a404d9803101c0c821101e10382001000b01c0b882c2c0b040d60041c02a00c0403d104002031220001c2003144281c01e9910b092000c82860b50000481d90303034130484485030280c241201c9180200d21000074a00550028185003905466004402d10032600c450011900c0e03668010407084103041680580b4035074040c010856141b40c01c812083c0c07020b41c00801c2d50328251241440c10042501c9410031380c007081c015081082182401442c031001800c1000f0300300117050505800949070f10026042d03d110001030081d40c1c042c4403003941140d40b0380c4ca001c022220b5545000d9004045904001244813440c140555480c022017408138060781c1c86400e550141000d012050015103a100c480301e0070541090b0303181c602051000c984602940270740080140103882e460704e01c800c01e0949000600c00b1030554200300040103015001410b44220b0a040d200108a200c801800b00348400c0d00f2800c00d41c1e21 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 842261330 1250 842260080 842260091
    0x7050111070308131403071d04060615020f1911060a050f0d060810060f090905010605100503040c0f1a07030318030518030a02060412020a0314010b040507020d0212090d0501 76
    0x140c0c0c0107140707040b04035518007030045d8213100304c0c104054aa115522640c1448914031491380d40071100041c115501621500000030029102c4107070341c17545140c1c440d10310050f9100383c18110392220204248004503c1641c80a002c002103655952070480321241141c1c010792010400950b6680a04140c645060300c0e8200c030303501d0b040860100000340185124036000c6000b100c1078010b44607414043c0300e068800141c040c02d034031443c04204800510b44000103403801d541e0b820010507e99105420300005405a0b900d045e16410719041c070407141411a401003582182907001048248900c51400e41b032000c1076161661038483c40d0030190007603c0041701400d04518504c598004040c0c100d00602080c4107035804440b5144124014140c1c3d440d0011006540100c0501c400c000c1030b21800441312401d44080c152040301a075903a6183c6001c030181c94183c0d0565150303014905542058072a441d446141840109000d03820180b0203512212004c2204076840c4000660300d1113600e80307049408106500500801c00e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 842262580 1250 842261330 842261347
    0x2010e031009030e12030c060f1504020304080301170303070e01030c050c0a0c030501050108070b090d022805180103021f02071a2101152f0309030d05030907050111070308 75
    0x2c08018008134a200360807911941100110020941d04560205801008107448034201202ca2980c02002c000d00c80c0140c60341225251194000380d030146203c1c4601d15100e5040c8013881071406d480220b5030030b20390b00a00801000c00e41c81259040003002c00e090000300c03e40506000c481620402e480e03548a0b1040c00080410800524401000c0342e025a00030010f9903211405075490f41001e201e05c0d40408030505c2181c03141d00c0c00078402c906c514401807000d1050404d035404e100f10100b031210303c9000c0303003800701c410081e6003040a003207a00c41c0c45540303200005606590014081c0410f48800c03542186450610040e92802008010046d0403007a24622205400020701c81c0503a2003090b000d40a01c607020440400c602110341100d0503100c100402c822560389280007140d0391442c0c10740644080e1400e0900020304481c544c600404403240780003541e81e4000e088141442e01d005054602e0412200b00104a02c2c0080480d00c28282c0f01c003442c0c4242e60410115032186001611741015180d1140021900f1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 842263830 1250 842262580 842262587
    0x40803070506060619051308120a0f03020f0a030906092406080727020f04030f030f0f05180102010204030204140f15010914031f0204052b02010e03100903 68
    0x800c40e2240e4201c502c65501d5000344040c60168688041c4601d418a450301d100a0042001e002040601d04204940302d5a40341c1075443c010b01c3d0009410205030004942c4a0241e0001d5600c809100c01d04042d8a40101d110f140c0081d031043c91105001c142c5ea0704910001c010b9150088205107400c41c04100c0a0003000612603110002c440540030034525040c00041d2601c0085468022140100c0410001941c120548084c0c12403804103c0442a820824006a1041070000d80301035406445400f2581d0f039586405040d004a4000742c6081c006808903080c140c40d80302044a40f20317503003003101150303100b107110040c0c0c0680100d4200941c094100114032802500301440540705500c068194441038880c030001100b4045c5402950340002c9910105014042c650398640710240e9010b02261800311841e2100b25440c4620900101180c0d00000d0800462400f205400c15841d008108442003072603040c0319074240c45807060000d0500c9000540d01e6600c1d601400b5034924910400001d111a80d868503000b07 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 842265080 1250 842263830 842263837
    0xe01020d0f150e04050304060804050a060c21050f0103083004050706050f07020105070311060f010303020607020d020a0b0a0618020301080105010e040209040308091204090605120319030b06040506040803 89
    0x1110090b451076000107143c07140c9482d6900072a04100a103203440e040c6901110104c1e0028001d44603071080703c00620014696203d0300303400141d641e40303404040040050041014058110502009090405110b01130002c4110641140d44c0a07645580e82d48443c05040b02c400d01c01302000806038040049c0c04103001d030942c540c0d441030b8404c0046d01c180589409007030300c0c0d074043e0310100c540d01181802410015402040249500d071700900b402c40410303607030031451031034003208545900d60052103000410030180c041211941221240c0060050300c0d4082c40029075542c941e0b0b10252180511f800400d4411059034003180c080c00801042d00c00c1200c0326403214001c2c0d4803e200740203032503180800000d081d030404440280600e600415442c60f544a50301e0481c0e5888003e020341c2c1c05402a10484030034002e5090080005051000021a55518210802c000b0341c51049404850380c204100c4140024404000c04280b07030824100003d40c1070801d40801d0f210b0180c0e400c925004280080c0110749414008040c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 842266187 1107 842265080 842265101
    0x6060207060504030b1b1903061a1e1918050307032112020c0706030e1c080c040b040b0711310b04181509080a030e01020d0f 55
    0x410649540004842c0180d0b0703080f540c44113407403500b40c05049c00500d64603000401c0700c0001c040091141c402c081404064105619074041c08904800030344503a4040c15440c1c81030809008000707416482c03001c00d00321003010406000641442d0000720401600d074007c0840f51403851f00031104503446000c03031918043c001c0c42006525100e8091014048034041c40c0020441540380c0700c6c014044030f00510f0b4111990b01f007132644448201c1d40b60100620b00545280180056036040003548940c001e9402c01c600540001500294100e8494054002c050041c0100c0c41401c59100800201c613082040b40072004402480380450554800074121403040a110049503021100740042e003103036940404414042c82a001071000e010000c0000b902c2041c4da881c0801803591152154180da0040c185507104140c0c0b98410410315440c2034041d9200321070f1a08041c04a1a00c45035100090004581e2 = true := by decide +kernel

theorem cover : BRFrame.Cov 842086330 842266187 := by
  have h0 := BRFrame.cov_init 842086330
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842086330 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 842086330 ≤ n) (h2 : n < 842266187) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
