-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4725
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:32:03.011792+00:00
-- url     : https://prove2.me/submissions/0d86c136-8c52-4d18-a468-c83178d35957

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 849640287 ≤ n < 849820143 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 849641537 1250 849640287 849640301
    0xa15090c0909150f0e06100c0c080604080a1106070e0f01050c060f240d06182a060504031101080912070b041e2f0d08090109080d08160918 61
    0x1802201c8050b17564000c120400e0080350302c282c0020a0603042902c462103461466101031243c03401c0d40c115500e540e0200e04d42001141c04075403e140008030342c0300c41078105140a01600d042c070700070704035881c08820060443d0302000d50140200005203d5840681c01030059410402c0c0e59021101245000f80d0016800803055442501e4100c0910350305084e074210b00c4012001006c00350100698400c159511402000444e080581c04600d200541000542d00c901d200035001d050400311903260501c0c5c1040203006100d51001040c00403c210030400a860315001069028003424607800035a1000d410905021a400c2c1d2181c03e800b002a01c90200102482881d01481c0900902c1d0243c145090016041d000480b4002d8280c03070410140d10580c0803e0a410030080f0394212047c4140e4240a001c41c0102c4490542110030740d02c08509480b10356402011a0024082c0400810381841c4282000c4c081d07a0f0064480c9803c1d000c9030100d40420703806170399400c0040c006019008004504007034070200810003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 849642787 1250 849641537 849641549
    0xf0f0403060f0f02280207090f0516020a0b071206120b091b0108010902130f0b180108070503040609020a1802040302180403050403060b030337030b0f09090a0f1a0a15090c090915 78
    0x1120403080040762000441000345644000e80d28ec1c0c0c2d032110701081d180025540c000c030701c0e0f254a810000c44c0206031803280c4115540b02d0046002903080a1000d00d041c6240030145442e10090102c85d19003036a40f01c0c0d50541180c203450001643d416190011000d140c030203401c0198400b00310080007403d0161580280496800c0c9403003000134076221001100e00340c0007074801d90000b440510100c1c001c6050f95110044041c40205501c4609135035881c5503590320a40e03102d2514490b400b040401c1941804000610f011025030315002c034500d8180ea0180c864066400080c0440e40d03254407001c2d0f02e403400c00450303102c82c468981200c00314450381d2203d91070442d144880038081c1c070180c01c00310b210390033070040c00d00e40240244494080310260051080c0540000c003403c00d10320489503084041440700744c011004c14015010142403069044088001200c0034001e60400c0786001003030300c00c0da9010352020702910095000401d01e0684440d0880351415103030441180113240a00d144c3c64200d003920324104481c2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 849644037 1250 849642787 849642811
    0x905090304060f02010b09070f020c03100902041808030c03100f0f06032412050102090405090d09060c031b03020c09090105011802040f06050f0f0403060f0f02280207090f05 76
    0x3c0f401da0403801da03160b80e1082d40d00000704c81d011410760b030300481d41662103038a81c1c411109804013100000307141000490702121280d0390750140805606250180c4051032a200252290540c1143da40c900c0c9440014403041a016012011a03c101100e841540003040f61100301c100d0552528131160440095121303007400b017494604d060541803085000f440c02c0b03809005140200d81c2c0b4000c8108114a00e0101c11034443d50b003044107148540e10791044074000c04020000b04070038442d0350005040d407d915041a001d0104038000b110000350312002d04040e0310464801055445254601607140082960350a640101c00b43c081108042d4150f00c03080c100e44040340c040311681c00142159080788030f50302a81407060401042400a2405000100278080301c0881c864508240c0d800340c82c4090304071350411603100751140441c0c03050780a82d0003100c5060507448011881c0100c644074070b8220303d041c6608080301103000c51100704494003d03c54080206200c44051085d61941807050000385411500c011150b1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 849645287 1250 849644037 849644057
    0x3110a030b0702060f09210a0329040606210218030f161d0f060a0f030b1006031b140c0f010504151b0804290f18030901030213090509030406 62
    0x10030007d1411051092282d003602c05030300710529100c007a407040d10584103040e01c03101c1e600300400103105125404445060201243da8002041105844065001c0b008005a4030005500b8050b140507002801c22440c000582d140140005004680035a14026034540104440304513900800b051030300203403204480c2d0060300d984450024058505003c05113045010f07520010b0125610071203000d0700600024217280381c080d40c6181204180131290012142d03034040b107040c401e54048402200000e00028102844941041d907000d1610000403021030080000e03071020424048110b07000c03101d10641030710669080e400007a401d18042c10060f0f4080b0345100c10b4408010586181d442004021003072404002070b000c1205004803030007000a0019a4051403072820002410031541e1003a103a80b03011010065249460302c00e40f47c00160040c03c03402441c0c6108542c04820717001104682c81c2c0a024240140c44103000d40510022100541260000511300001c1c82002c1e403000010300b0460b17445070313915000a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 849646537 1250 849645287 849645301
    0x23060d020c070f08030a1815050703030c091d0a0f051008121218120a0f020c03070324110a030b1509310510150809030403110a030b0702060f 62
    0x400691150004c207800034015818510311440d50719642c0011001502241c503107815100d8821030820190f6000725100040c01d008168150040e6140c158003410b0418003d843e2480c0d040175109031540c0348501c2002c0400251840310158002c849800c1003441c204581d01d00190440f4642005015595940c0305c0c004a540030702041c0d4040b1007064a40d51068101e0707864080900760404107141541050b405900c1800d1a600581c0000d030103071500d5960741c030380030701c181e8071001e030500650340b0240d4025000820280085203000c0c00c6064821030580880c6404100325150b1002080002c407044d18103540000c2c0c41c003e081d41078104840440c0b0031903144c80410840d240f181d499100340c1d02c3c4550400c001c0b0007028034805840c941d0f54100d403105128a045502045000011980103e41a424078a50080e05014026101000d07150090360350415004500381a43c04551300c3c0190300c4001c042e0014a075603e01c1e1a110080184000c5a01085034101814840d1001c0d40340c1c141110403006401808002801c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 849647787 1250 849646537 849646559
    0xa0e100f060f0b0403230a1b050603091203070201150e09060609091c0e06220602070602070b0a020319090509061c02010f05160f05060a02040b0423060d020c07 70
    0x40f00d95095030189424a550b0f1400b962464014061218480c4144901d0302020140701e0050821310071007042c02042da1071882032248400903000b50740a50b0003170081100036000000e55260f0b0752920300445403280d495507422030150039812032312482c3c0c00c0389400000321000c0c0075208070300a1010409440080c2c0e108414807481000464019246038001c0c01b9182115450800d461740e0130b82140b44c82c84080704000041500b035402005100b10342c1903490b2944035084074075110207000d01100d1003d40012464600000d56811a501448140450000b9101a00341c020000ca80140d400c29410280720500d02502600b600c61510031180602c00b07000001d21503180584065101811048014213154107980046070080003804286050040800c140c20100301c04400040c0071911440c28540004240e03c0c0c000c3c103100001c2d0400301d12900502084c08081c0045080d1000c1e2402030102d43c0c618100303510f204101112102d1000e130000f100107000d01c00552140c0080500102e0201111590ba0f51007119000c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 849649037 1250 849647787 849647789
    0x1c05011401090203061e0d0215030402041b0507020f120105010807060f050708031f05031e100903080412020304030b010b072102060601050f070803010824130b0a0e100f060f 76
    0x351201004c0e80e00c4010000e0009810404800601101f10b1250f560340410602140301c403a51348002030200412085280c607005215000014000e03180100c01e40e2540076215019405c4000c3c4143c020703d107448542d407160001081e0202c1c0d100004d00c1556580c181c59529034580d0f014190008030003040c084c0e0b81a009108071540140c2c010300e51441c1daa90000005450794030b11b136120827041c50303d500025140e5000c02010841e0340d6489458a41c5a40c0001c105261801c04203880d24641e0811a04a001c01d40000701594000e030030400d204c80c01c0d01300802c00c070b04522070703500700401c0c10f07800b10b002144100b0309401401c5418460356031241c02d40f0700c58a000004800c017080000c0160303c00000100507501c03c02c050030000200c81140c906150180d0b441c4069a00243c1110078182d01480c8802003181c0035200c580d0800d1908074500005060210142030701200c01c540151900102c4000f041d801882030b440210791201c90002e84404514242102002d086040d2071401b003d410018007091030410902418 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 849650287 1250 849649037 849649039
    0x108060d0609020d0b0718150822140c010809070b0c030729182503020d0813050a0f06030b0d0501090c0f211202030f0301030c030209010b07050606040b1c0501140109020306 76
    0x40b80a81d11113011030708034400800c1c03500c0003075000d0303039030076041e80320524603501c2b00e104500445090030038040344d074a40f41800089904010441c07050012094002c205881921101b4840698408003461914030b1445541002090b030501a84510701169400044d50280611400c5480d1507803117030000007036011649080c40006402c00b66000f8141c40031605020f500c01915015000c1607079803500015418800c029066588150010700c214806205010382c0d40600011141c07424014101680c3d0410038500340122400e060fa503a040140c1da0340ca0a000184891344007009000ba403009240100144110b0b1240001c0d140d102c40740820740841040c41c142105031480140302a00a0741c3d22210007480d00c600341d450640c0010014245c010900c103008601a40c02203040c05066451803050100042059108a4a0b0b04003840320f5800101d012552a403c08811200440d48840310000680814404030a1000280350001010100001904400c480b0501d20300c021b181d507030382c1e056134005a00c4212205 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 849651537 1250 849650287 849650309
    0xf04080109032312100b0a0e190803030a050403050702060d0f0c0801120821100f0b1813061526060307050d1a0a021210050108060d0609020d0b0718 65
    0x24201e40c49151406680800250083d48404d6546c1303001d01c4c0b1581c050a40400064100c55150015040c254511494a03c030b0220089181e45854600d40e00d9000c00380900c4451910341001c5402c1c54801c4040d1790400303400801e060b43d10058510b507200140012414480000d04040184130000d000300015412200c0c21115000440c101e95204030b82c55015000c0035071000c0d089131441425081d00000c0c580306042200149207981c0c180b07500030043d08800d0740404015034040004446420040c034816018140954040c0107103031a101001015100a41126600040082c0842e01841c0e0103806911040c124090703420b20103c6030340a09540036000c0b10310b0350f09940070500400540c1480c208214010780582980c01404e00c900c3c4c04011003480554400d400d80f40c01144155031000c00910741600b28030269072040d005841c05c00081d20441005090610809843d001141400341941103828529802000360b060030b09145428256194140c07072500005034100c0e1018140c040c1d080c04903045d640d085000b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 849652787 1250 849651537 849651547
    0x14010302030607031b050c010e0106090c09090c020c06030601030e0f01020a0e0409110f010c050706020c12030a0f1d091e01170a02040c0c0803191109011b0303020f040801090323 78
    0x4192956405021f48a541d50340c2d41e04620007801080c41401c029289040010501d0f5000000007001513145800c50305c10213190100c804403040d0002842180c280c02568280d48965500c00182d00a0a0f540c0200d0300394011006100404c040c1980100700845103505c0340300c2d40c803100c2414070007101c1c8c4442c002801c500a42c0b00a40301450308204100807154140341c247d4800c5003d544450418066610401c0540d01c48520410b461070800300e100444036202004509040e19004003d285604807110300c0207111000200204181a1400414200310302400846c424181502500107400b08400d901b19a14040c2002044101c01417042c0c480c50b01d000001001d140b480c54081100505554070007005000400c1a110f0001d894070020b5481040940c2c121004460010840c03000c2d030300c9040034040c0000342040302003101d17078214020742c45007424200c0c642d0200040303141c154000c0c0709001440102c25004540000c0070441500440b900a1003540e45010150020742d200d88010881100d1080752241030003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 849654037 1250 849652787 849652841
    0x2180411120408031f080c0306132001112d030301060c0318050409080d050601140729040f1502040324140709032325091401030203060703 61
    0x550340201741c00d240785001c01003407500c20700c81036041d50004d501d030780000c4144621454240900342d03010020040c8848850029030b551440c02c0607070641c1d8842035409420141c0302c0d0b4072440880604075400070480c0c16401013007440402009019410320a8068050301c00c0c0b45002010094a040700e4490326801811040c80c0e400343c07421a110315010703002c1000d00100141c903a81e54000c10806500440e0659502c007400c091130f006949004141e02d060007091701741c2415076401e420855044036040b581e1020b0100b0500c00c0c87c0d2040301a44001102d00c00d00c00c05210501019058600000c0d10900c401d949450000d82c2e480c080e400742c1d10014011955400c0c0140c1005410458500110030407880090611036459003600b107100160350070b0000400014040c010000d0f00c090030480d0508540d2a20203800d90291482d944000e4402c5600070080121010800c2030b411100c0d440c09892002c0050102c6903001d1002e500e44034007440280e100c2c3c07050101040009020b0700c10503112000c6001c1d00d84400050f07803 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 849655287 1250 849654037 849654053
    0x7120c15020d053004030e09010b03152403010509011a0a03020913151401140f161401090c0b0711090705040b0d0e151905040213021804111204 63
    0x50b0080000403001003810700a22001c4520302c0050410403440f80d81842d05005004c80c07051a4018088e00c42e510040c483d50780c01d28103580c0d01080001e5090070480c80b0001180b0442030802c00c00ea000c032070b503034280c8405003035400c00f0394140c420aa83c5075500740c4c3d039030030b01c0c00c55441d00c60182d05139076904102ea4150396100e42c004200c000e801420403034484407246a17034030450300c4103a4801303042c00c1e846030705003c048403410f010004404d00346044441410700c608403590b80c0c420032040b81030007480003650070141e90f0446d12408456030884103245100c00d5000c001030203814058402c980e181440d820205461242c1810b1b0340d01c054004025115400c140000d018a05002525103000c0c0401400009079041c991070084c94100030104c8042440329004201e14500320003c0c0317a00814440d003908000e4030810045019410b0013045c50003003016103490000c2042280541d03c942c2e5007074000110003903240013441e40022007440940e4102b0981c0d003450300c0d4184500403141289040c01e004404500814114 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 849656537 1250 849655287 849655297
    0x20a0317060a030b07020604060f0c08010506070203010e0303090d0f1d0910090914010b1c1101120c0806010905060906390f060109020403080712020109020307120c15020d05 76
    0x90610a4000e4403a00d40c13103060101180c0b0700d40180e000804100c00c10905010340300781501600014018020705c00b4014046035014010b40d40590b4010420134107540e02504501a55841e000980380c1d40d06000d20307505d455622031100500494008075892911510484400302c00040b542c005460f10310000381009021000940204070701030345804040358080c070900c600103085100301c01c6a10460612030400e400e540c482641c10380326000c0c0a444a00c1c8903c0303041c10340f040d1640a85421800c440b640e0050314561000308910700528507100007602403c0c0c12480050180000b62a15120350b41c0d90720800c07803c1d1042004203600840d003030200e502407840782e108016401c0011010099112001e003000002c2500401740c0d6141e5601000c01140346080030305c01c25000d08402502036103030900b1901c0700c1c1454820040010301840c044c005441101d0f10030740c001c018045e801001c0d11110383c1e030351801039000d203030860342904c50300481c40c0c2c00150407000b2290ba42803000b06402420f0722400b034040c19038858100d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 849657787 1250 849656537 849656539
    0x1e0507020f011e170f01050d031407080a0c02040e010915020c0f0a0302071a041202060919030506190506030d080c0d05090304061b0b04020f0a0b07080415020a031706 73
    0x100548240f844040002c40001d103c03a20381e12490f584070003880c4541504800b40c44c843c119030b900030050100c1e481c0d800031802c18075058180404903030400c0b681d1410034454400041c140b0b02021400d40c0d80c090b480003c0803252402114140300031008900035500302c0d0182100100095001d680003e50822141c001e0b00d5100000e8040da0005c1c140c0e01003d904180c01c10030304500507001984240321a591128030150001a148807003170501e424450320200c411040c01012f40b29003008a150b6025507a10241007103186015815196191b03076038074219507100000d40b1828481111030300056455840d911603184103500040080105080301c0c103003915803030345c06802050309800c10000c0100b25001400303014081d10b440d100075503846160110050001555030103071200392104424040200c1d1000c1c03101e0390003075011a0800e50111800000400071951036228050b038040218146040c0400303400640116400b000044060006c80e61040703850b0981c1d6003006022030f80001c1c4c0f240360300e4130700100184d00680c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 849659037 1250 849657787 849657797
    0x70f0803191103040e0f06090906010f180f0f0f0f0209010e090c0714030a0f0c05100b040f09030201020c01060509060d03030207050c0607120f0518040f110a0801061e0507020f01 78
    0xa00e03070740003490651088501086d01c02c000800d20080d41044852142c0c0f040307503140a04402d5050028600c0401c155101e03d80500c82c0c00740c901410021183d11800080401d400204459007018401c0405044000d00305d4007c0752402d51300c01c9002c1d401d8000c9420f00e60059586035007d20300c0030200003124002514050715442d00340400000540d410380c4000035200289c00850311030443c280001c10040425a4020811045081950004000040390100b11213a42c0d004104080190040303002044000c00c1c512140e400c107042601459010740c014040403003a68028440349844c0d10501c8a6400140e50301908003050051313203c08203100380d01900340c80384682c0c00d99480d40d00e030000065558000300c000341d035040940d040041d05036420070711841c002c01342c03414101c6c10405001090440000c81141d2180180e4581540d00c0000750940c0c024a0100e11514900c3e44418a040307000381150340900405010800017a0f00c0303031418402d220402000c80b0365980c0d0600d458560782c2808002c503500150030341481 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 849660287 1250 849659037 849659039
    0xa0b01080706210e0601060c1e020f01030902030109020310020409050c04050604270218012303070c0f0f0b06010f172410110d09051809071502070f080319110304 71
    0x94051040500070482559036610055940c140746189d081c00f0ba213840f5202c01490322480050f1a001e5000034441400d00300040c2d008440d0000c01e000d06100c0300025454000c03010700455407140c40e4050419070f2550f03141002150f1f121440c4040c0307071245015182e408642403108101c0c01014116117078a01c40501d00b0b61143d40200012131050307820203094030403400d0f807214000c1d4031540e01007a00310300800d0b45940580c000c10460750801b0644000740210081002c0c604212050080d002e20b03403c0c08551100035001c40d007110b818403040001040d61920b0014114208a40350948102412212510048040030813500c40d0300b121104002000441803400f44030400b144a55501c2000800481d90310352241030182050340d07003046c141001058910705000c070201d4140304a840710f0860710101c000c02450001d894544c0380d5034a01c1c10419501c540b100d9005010942052607021910700100c400b41c07200e4182041e255800d031078403402500219202d0850400081c12094890001050581d600e501500e00d40303 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 849661537 1250 849660287 849660311
    0x31518061902070c09050c070b092d0f061602010b030604171819050109052b02150705010c0f0503090316080915071b06050a0e031c020a0b0108070621 66
    0x2a0b00e04a46522003400c0106928003400180c40d1022b81c8038152002500c1313641180840042803400c1a4031060200c4401010720200d40c1c01004006100c8002d002101c1c02e030301e0104484504e800841030b800d001542080d00040d1a8100059280d014590100f05540041c0a0071040e04c1e0b607800002c44030b440101f000c00d002045071030311a8060441c00d8041d000b02415420b1a00240442d4400c3d40000e00803070700982c449411098011400d00c000109101945400c031042c000241c08003038624401202c8039000030072400b0003605500614510f80d158940e200c1c9006611801d440902049451a406070010400c0d440c89a03a9100b420803810300c5954118240f030a82c0011030201e031030391b05143d8082500040d81209012184592081011310350307082c00c042e5810214010f00c540103190120f0203210140d10410819501803090b43c6c40340c2c4000715091540402c03d50f00a5413080b08200c1aa00c8001d0b03000041609040480c0e080140c80c0da6859a10100c9080107801c80048131040629000558071049000d903 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 849662787 1250 849661537 849661541
    0x51902010b180405011508100216060203010e0403030b0117040f0201110d270f150909181109040203190305071e050f07060206010e090c031518061902070c09 69
    0x21018001a0b18212031400d03140072800c5401d0700c00b45509111204904100700607000454404010307041c0c00160306ca14622540d070032384d00078425004043e00d0009c8000f04049140c16500d80c4a1400b9540601c00c01030103800540c0d440210a0880012010b00710000d00030558034500c10004503c10b25045104000190429041100d4202031400180c01e2101a48501e1050030300f010013200c42e11b00303541d4200c1c5000010080c207401c40c070070260000f080c000303000404c900901d18840100326208083c400141d41000d0103904142d0010f088440000b0b00940055500304418024450799010b8000d00d02d205c00b60505184031a8400d42c00c07810850300304859400161201c0141604020100000c0240398943c50100d0801c1c503034802c4003a041d801640e00b048241e82c00a40f05045a8600789000341e9a110310b88264180441c0b4024140c1603c02d02e8090103c082d038110a8030b12444001d180820300280b05d1868940300c190030360720340309000c0000d228100c2c4102c00d50b0007803603914803c030015440da036038503041ea0007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 849664037 1250 849662787 849662809
    0x7170a1428090f0f0e2802040303020304052809180812060f0d080d1109090f0105041d0a0206030a060e04210503250e0a0e0103020a0b0a051902010b 65
    0x40403004100441c00f8400c1030300f4060003103007407a940c0c1d5509150420551180003011000c00c2c003104021841c21400c10702075200e0003a0303132940c2035541c2e82d141c0c01d02030340d69070151080a000301051034280a0f1189101d9210070142061860301e000c061601002c0e8010301442000b880e0842d51a40210f8005241c8030020001040c1580101d4206c0c503100c1c0800072680010794516001d00c2200349a500014480d030202c654805010380d0015048403901c105928a02034180c44a4002b00858184106078440b00e400e107040320710454091000004442049a511080e100d503d0040c1d804403003481d00614001e0003444d8021600b82c00003c201d0fa40c2c6803903070f282d19010b0f1816528142016420803a886001404034940b6103907061440c07071802c11503241104251241080408900c43c13081a500f550b10030a0010811200202003403075803a100c0f09240b03080d030000e200807807240318403e0700001c00b05c902c14191b030080f08450300c915060419a8445043c0341441240e0401155607074050341c04a80e990341e041da1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 849665287 1250 849664037 849664117
    0x20102070f080c04060806040206031f050d0311010c1803060f0b031e0d081302010c020d0501020d020d1a06091509040f05040317043f030207170a14 65
    0xc92040342072404d0004580d400e40009400c0c0d0402c400700005600e0b40000c60f60428886c40f0303401d4040d80c0e4415075419070701c0140c2050768410500103000f400d06a02c10070710200110240000c100ca081c2c290400d85408521030188814504400c00030000304296511161010444000100d103401a100011381021201031444c020507551069420001e002000794a96102c0141406540c03410a4034050f1410003100600a04000b40d81d40040115203500d00c1070300507035030b0002c001d40d1911100da039068040e400c00c00c1c070012201d18040c031001d203001c05040600160100039005510707040300141800340307808505011650ad80d50821542c0e945844a10800341100c0001c200020141058680102005924441004590780718400d00011649040c030300c0c3c042c030b480f510101a41211003c4000558400c50013022500303512041401d2895070940c000f046024426a02080c411110000d12100c03805034000e004009080304c1394030400100e04100609508412507003405210b502000d6458546030702c98016 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 849666537 1250 849665287 849665293
    0x1140a0302150406090b1c09030215070f020d1d09130b04150b040b0906130f140106020609060c04090b0d02044104120c020303070615090c0203070609020102070f08 72
    0x100042a44444e10b0406412540451860601003511030300c00b00b00c019000c47d880b580d56882200c1050b000300000d422883c0307412964081d5183c03000020340b100c000010b810000d4040c0d0061440c02030301c508000c0801c0e0741702d00b1036154081c100400b802404400140103590004c0c0e04180f040c080b4140d00c1c0c0481c800c2e88525420440a15407012000c00c0d52081d80c045802142410000b224a07510710368299801081950700040303021102044c0c001610540c4400c2c081140b0b01080c200c0020007116200341178406507021140692944074903144c1e90074007101c62180404c82800144038400d030075000016801c900510621030708005400150490b500d5024401903011150602c2080100d400d060344400103003c0c90800c0500c0d0548440d00700f0590080c40141081c6451386411403032030203100b41622141d000340c222500c0340b695250100040080b01a066043c103510340c00001d80303a01e00d00420354040c000340d000c3c604106440e650003000c1c0100280417410350040f50004101040f40c0d0f195070300140703414401 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 849667787 1250 849666537 849666539
    0xc020f0f0d1d090604150b0706050a0e031611060d0203010803130806090c01230703050d060e0c120403091e0e0f151207080102070b15011701140a03021504 68
    0x805050340340da0307900b440d82c07510300e10711100c000c1d80d14900d44940c8031030180c0b4041800140f880048020402035004510704440120f0300d00300b030203030744d0340858424071008070204000c0d40742082d900d90768028101440d042c030000c1000305d00002c0c44c1c0c4810040110015280a040a507046110001c2e0f8100b40c000c3c6005500c0405d40e00c06030010041c0f00c0c8010240309014200b941090942d1b01e4403100c440450038103000b420100300c11410240b1030700c12500e02c400b6002649800f120324005140d9881802d8900c460750801e58046171840c1c5a010b018050712060700c00c14070f004410320505401d01c200070810340074401410b1000900303c5107140c400041c1d4070030429000c5c0d0f00e0b06151580d546c03036501410b40d4105084a07400c01c9150005980b643ca00100304827120a0040304620103146082d41c41d8100e00300550020035040c0c100901c107946d040c000c034540400b82041c3c00c0d10100444400c007020900010090300e540041000d07116210003880403207009051000210740b40d40100e02480701c07000c1d41d24204079002078 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 849669037 1250 849667787 849667813
    0xa1407061a0111030a0507020109050618010809060f041218030b07091e30030512010b030f0c160b18060c070f03120209190501030609090c090c020f0f 66
    0x1404001c015003d00f48a41142c03542c160032541c2c1d008045119050000004846017568042c5a6000041c10010704259803a9a10510370744400c41129409000c02d03110720110340040000300340248520984419101e0690340e030b442d4512030701c0c04405050141f04120525066061825510b9009107008403038030b0030a070605007001402e2810381e0f4040c3c4220b4980e802c4071074100f0038042030481100c1e202c400c04c501e40c1c03c2511161010034074407400c0300201100f00303410034105908100070b06200060b5004180580e82e951402c69490b200c211a0341090440f84000242d2483e0027201511a030b44101d0035400003940c1c3d55a40070040041940e150082107003003042e01c115544d080100c954020510803501e800d2079080d556032400301e21032800080602001001c1d07040111020b41c1580c40340c1c00003d2175040088008040e0035034107801070060b503002030304014020404030b4880c0074101105500a5141c40c40070710308495000108a02500c81e411400b81030341e502c0b840c610801c00340c124500504060104042c1c0382c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 849670287 1250 849669037 849669071
    0x30806150901020703080703090b0d0e011406090601030504050f1207050c0f01050d0c051c1a010333030b1e06030c01050318070801020a0c060b09010b03010b0a140706 73
    0x540356089152080040011a0760301090030300031283d0203001c8581358610b516083c2d0f00680e49420a141c10500072414031410fa800343c1009041480c2c01717008215a420100c40300750819000c41d40d968110b6501c1700802c82551080d840558414040c5054072102c8640c106201c0c2030098409004c104c08001080220a2000c10300c226004208200d803260340203d0440c001030540c5c01003550b045003181d41c03a44526031150240040720030000041e46181545450b000303184004000142d44030a042c201700402d450b0b194040e206140c109001c04400c2036038440e6840d02c1003c42d203039112400012100f0104004002036031890f8030b0f40550070140d035000c48504281041207140b0300003040e06210781c1c404650501d01c0e981103411660007031000c0c86090400802004c20038501402c1d0750103400d0542c0300043c00040290f2201c42d81716024460507060200000c0b0381d04200d003032042802a594034103004c00042200300345010041c0049110303410003a407812800b000c0002e00f43c1002d0400c3e0740442d1290300b403400401c010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 849671537 1250 849670287 849670309
    0x252a0c050303160f0305040e01060c060c031a0f04020f0301063207021017070503100801061d060a0902031510050703090e0712151509061409011407030806 68
    0x9600440c20000200d5076010b0324411110f01803e4a001c1c1c1203840c05143c800c200712000b0f0240c50080d200360b543d4804000301403140c10300c0306454080c6803642d4141680d10034050752240040030b907841c1000703012420400c030303000000d4060305510990030031002003441d58901c043c500130481a2200680300b0410442070003850342c1e0000710500c50744004c0041002c0e40300364003070341c40d42034042e640c0001c500c41d0303a101540d11001c000308083d000c0c00c40304100720100d94040f000794402d02032945520038a44d0b80303610b054203940c1c035405800d0304409400c01c26403500300301d0b0a000d0341c000002400c0c19070140e0340d030110104991090750007280090030758500022504003000e000030500d040f0300d8201d14180c41c81d1001450b031400c43c010030b61141280c10100e2010b520076407941c00c125011600c2040060103d5604d844100b00b540305040c0c4880190490481c4180204001002c645003501c80d13280100c0c00c0144240340798070100025050020a600604103901c6400140903414880c0c0c9502456080413010000c0069034 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 849672787 1250 849671537 849671539
    0x2060108030d02090a032301150b0f0d0b0a0305100c08040201120506010207081006080c030a020121020d09062003060a0e0c0f03040c0f0509252a0c05 66
    0x14000400400c080002101d2118203026001a01c030310b40c000001c4d500900662025003491358081088204038040c903000882043d1110080041c00040d02c0721001d2244588200c9060f1141840340c200c060217560000d01101e064258000307005021000001e516600d1b50300241d8191b48201100d0507507664502c5610044032031030034004000c0c0303000d41c0000c20964244058400f00d80e113900215071941d000308100c0001e03007030140035601e100c1d2601c3e051034000c10746031040300000d115891405507142404901980d502d50184d40c0c12190820741c5001005c20450603039042d00141d401c1102d81240c542c03034811a80707420311512010801d9191509600c00c400b01440c05a01054001c1061001a540c0d030304241b003c6501c6803071030654a9845809c07007805401803240c15031190400104100410a11612600a6801c0134010100c0c5507141d0003400b20602e0304640b206070000c2e003c10309a2441d0784090304c0c660750384600d140c480400c0c40c0c8814801030310404420802142d03000c4032101070422803c1d800000180c80 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 849674037 1250 849672787 849672793
    0x41103010e2104140d05010608060c121605121332010b01020d0c03090909120f050c030a08090a06060b0307110a05030f091f090e070e0108041221050a0c02 68
    0xc1042d0030311048500c0301a40e1482030700404082010006c0a4200c08005d055650545c0c8592802d0150b5114551209071042c03608003e1800007a209240300c108052443c1050b500c80d41400e4221065250780c1001421051620213800f03c4400003608002540202407002c00c8030300c0c5040c071640003c100400d044000302940740d05207c8072183c182d070300044034200094186041060300000d070405403030395803040e08500000d6003001080d4041c40314510307074543c11820a0340c42405032020a42c0032585401010b2100c03035260410044018014031890b4400e42100320401600c9284580e6034800b01282c14075441062200b0000c030400a18a8101c80607080660340c41002d85204c2c0c075141d0762551a4840d418008915041c0410351411039180d81d44448a10a12501b074035078040500d0b00082c22118891080300200190480002d4100c0c1c230407101c8a02c80001a10b0b0302040b5103d0f9a00c7c005180d00c04064441003103000040032490001c442a450004819028006501d05080c00c4c0c0c0c0042e6841c541c940c00c1998 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 849675287 1250 849674037 849674039
    0x70b0a020a03230f0c09150405030c090f01030219090e010902040b03030a020703151d1b060702030307030e040f0906090b070206330603040b10050901150503041103010e2104 76
    0x40c00d5445030340b10003441380214103580e48400d52055801900081908103000200824942c0e800e0401030023901c00803011903ca9103448001c12030b0301a0100d0b0b04140700041c050041006040000c0c4804000b6510071080b2081900d403001081203070074240c140d99081e0f440f042242c0541c140b9206461401e00140c0243d13140c198030040c0655980750920004040380c0f42c48143d603c13000b1242d03000300e080f5918624103d00c0d010744501007a1391155440a81045512061440b140c2c07071800404a4030080d44c040c0240d07080585503201a1210811080425049920303402000382032041485600340503881220000780f40500e5003082c00055500414100556212406204000b83c0d001300c00c010701c1000090f60a80100c0180002c1512644402a41d030404808410b21040000e20031889206a11114220451a03918820440911401e10030101c84200400442c0e1880c3d2091004580c030900465039098540071400c08242110300540b07091140d03401401100d030180070701910340b005d0403914064050030700b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 849676537 1250 849675287 849675341
    0x7020102182716020d030203040c030b0403031119020f0609150c0927060f060a121503030c211b03021e030a090b04030b060904020303070b0a020a03 65
    0x440840005446618030001404410700c284100441440b45440700103424240504140c1c2461081640c910260081180040304544a44260f922850308258a00b080910b1520360540d400c03800745c803d80401d03440e41051100d89030080003c21001c041140c0a00c2503000011009040c60b000b01c11015043e0048010302c940b1800c000f175011f03a8815940030380c205c0c503200c41607000486d100d44c0c00d4050b003002c4035440d08107415400c0454200c00e5188203070000c007039039034410030001003104508280303910001c14008210580e20841e1502c01c1d900c403c20707001800d11340c807980914000050364421000a00300404010400c0819140e1280d841d03445510f41c03443c03220046001e03125496140083c0e03021b100705002d0509051080003800a035945001e035100700115102881381d1aa800542100d01061411100144c181c00c9441207504598000d00d07185035a071076403800c00000080142c0182d0f412f1006004880209058202040c0500c81c4144010b81d141409400502a5070013480094078105041d2011802 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 849677787 1250 849676537 849676567
    0xc010c0302041208280513120210080712061e0b0c15130b13170c060a021b0319140c4804050c0a020a12170c1207020102 53
    0x69540d10450054650b0080400001140d41c40065070091700825510b44140c0394100300280405011640c80e9603006403201d10900c06846031000c0207402c580301d40006108030f8071460980e0740011507403400003058040c1503e0001500d0107900082030088042c13422a00804101d0300181c014100050700c1410481d405030f075940c480e120401980071a040101c0042c902449030380200111951022060344070f800c101806030040140c1c0c9004803178022040c10000060303155041503940301c2d161040205000d40d100c00d00c0c0800b0f5004280c4003050503000000b035482840080c0040d00c840403048004130703001403503202c00400172841601d00b6020f40c3e108120b401d10315032005c900714400c04044039030520a034440405e46607c0040d82000c0c2c60300710b40e4229120104507107a4400b01005042201c0c184540d85071090003078004d101d04185400540d00c1801e03035200045028107004160301c41030400c064050922400a000540121410240010001000131094074040c80007900400240b0003181020b42098685034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 849679037 1250 849677787 849677819
    0xe1c09080705100c0809012a022d190b04170606012a0318180506090108210d2a091406090409080705060702100c081303031803050c010c030204 63
    0x412881c00160911b02d0764000c0d581c410240800b2084100d0403180c1c0300089109511080003203201c0c1c0503a032498000e05400c647c0c0821200d4072181400900e440d840d04000700280a0068030504211003980000c0b8140f02601402c000c1c69844031220014468880701428600300418960601145450680720b040c1c04140c0d14080100c9400301401408032070030152480d0103031503d001c41101c81c0c2c03d8041500310440c850210700f00702000b0180802d4459000300403040c8800d0050344c1c0301d5070144460200c2407a1102020b02c0054001c0082440d05045505400c00d995100300415808035100c00020b540c0c000442141614001c1c600e01041d442d0304003c4400ca8151065504078801c11000c1116510756403903506c08803120364020842e079513441003450705039210801102c005015010f00010075502c40d00720300494000d1a11581c44101c580d0302e0100032903003000028030681c205940c03065032040719220b6032413a040170742c06034803501e88410403240c0c03150a4451084a81c420980188001c0010b4160310690350 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 849680287 1250 849679037 849679043
    0xf0a2001091202060f0711010b100201150b0c03070201030506181f0902130e090c0301060906060801080d020d0f0509030f061911030a0b03010b0a090e01200702040e1c09080705100c 79
    0x34000303410066010301602400c09c159a10000c2d001d450450780b50151b0001a03090700d110121801581e40c1c10080036076000d120070101541d081001004015882607001e503510900003441035481440c0301c070415500c507100311100800c20740b8501103a1544105500700c44014443c28005518111312090305611021032881442407204203403001c100030710b00900c1142c0038214041c0c002c1000d00d64481a10015084511074440845c2055001141c140b0300860040c20f030b50295001002c00b102146011203040f003440003050100001801081c24540d41446212128002000100803505101e80125a00f803000c0912000080c50704101055000e4000c0c240d075403003400c041000603205c0001c40824094902c5080c05548415554000b14044440307912003080c0c4101c2c58020005c80310121141c0c1c0d1398210b5403055007001842442004018903043c1c0000303024a850400b51100b0303142100b0b1002d140e01c1e4161041011418000c01480354001c1004804028001201e0071419450420f5001e801c01c1803250f00a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 849681537 1250 849680287 849680297
    0x509091009050304081005160504210f08030708060102010e030915091201060605031e040308010504020315090112351e0403140c01140f0a2001091202060f07 69
    0x701c0e05105040c425140100000c0d401e80301c2c80810051910000c040446907400d0352118289000580ea215405583c10342c0d558103800e501b4100030801c241d079080910042102c0c0481c292032120001001c05020314003d80440d190340e109802c0000029003501e103408902e001c1d551083c800c001260782c8841c0d059400041903c18290b942101d4400716103201c0c4540c8806c4059070170a100000c4040d4403000452058540d03501d5100151a41e008020b02c0030001c0e54047c0010301c05070300500c41894164001c0d82c0064100b005a00d00c0648403002c140b0501d800d07400703071110f03031032a10900c0b0500203400418810050382041038221a01507050740901c0c1d01549000701442c0070b01246481e131148449544108124080c40d819480d55074078a001801421801401e0b0001d000701509504e1650252881490b0206591200c500384007401010700610380021142d80300300000303164001c0c110411424246200200c1d100041080c01d030b1401d05841c2080c0310040b800c02c641c0715204100c0c800c1d401c0d03044103804c41c50610300 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 849682787 1250 849681537 849681551
    0x150516031b110c060a17090a0c050103020c03070c0905070e030a02150c0f010e030d0e010c021209031906022d091921050f0a0f121b080306010905090910 67
    0xd580c070f019440c10a890700010700250858a541e04030702540c40312441c0304020361040d80d50540603501c07800e030850000c00550101009112941c001d8002d810707100317088411241468a29100c0d08200e0082e94010b2420311341e1041802005903102c0801c480c0340109030f009100c1007035550b010403901c14104c5ca070103c000f00081090785c1581400c1c0301e03e50420010100900040022800b0b5548030390003040340348400c0e032501a29040100042c01007120704900c5401520100c17038540804a1964048900950b160291060360b0070480d080b5600418894001c2400685950f840400310002c100c000d90791901c1c07802142c402e200d031407007080225a42c03444142c5c3c00c0c0725006072074803804440c44019084041c01c2034540f084180d072031703a51711282003c85010703030201c510f07000b07130001199259207a490b005009074100c000f000021407108100c0418000c4207190030302071030b04880000151240da10108464000001080c8149580d100d0311400140208035294005810442d100c6a507561405c0180156140c950403 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 849684037 1250 849682787 849682817
    0xb01230405060705011e050f061011030c160909020604230603070305040201080a0501260c040c020706030e07121b170d080906040c03080d09150516031b 67
    0x54500a241c040d000c0d5481d403101d850322074082c04103031030071151294228a696021400a006043c0503c3d4003e000801903102c417002e100d0700e8545ca00003681400300c4041840c0c0d86034010402010305141480c003410040c6000d015101071026941d01400e4004e0802c8586005030f81d030f80d01154100c550300e5101680c3c003d030b00c801180384101403c0c3e080754401e6001c0208205130390181c0200384030f140b003641d03051411303030322400485d003103c500307010702c8410320094040c101c501103210b80f03400400c240410803246103c002900040903541510140401600070140c200003d81d014018103d0b404414009007241900707081d115507503030400310800781210240802044040d19542c28075000741c0b0002500741480d002d02c418059484114000e0740d0005000600016449a40410907a00581c0e2088080d400f440c0713581c41e01c2c259a00804007041901360740782c3c50880003428030b4800b0000b00b07000e001c0104441c5000170085250501d0300c42950207250030706414401c0d180d811002107280304e4090400700305c2d24517080c0c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 849685287 1250 849684037 849684107
    0x60e120f060f130503030c040501080f0705040909050102090306013305030703020904020d1d0f06010b0a0e12032712100c030b1c060b010c0c0515070501020318070503010b01 76
    0xc0f8000d807143c007002040c40019182d04000b482924401e07203c2880075154008a03100d456400c4469000144050005005030381c1d0a0704070000060160001500b03003010312001a04000080e808100018900300c141b003103078440c180842c08040ca0010502c0740c903440b0f8000250603403000801e000c0c2019030020340b00807255510b0341a00e40100008404001c103101410b881e42002074070000c042102d20965101001201002500505944a48150600b40709500b001030b14540c4001c0d400d90707482250b655031001402e500700064075036010144074041c250019103000403201d0400300d003070502960110041c054400f50026204601d10807007100010450240c140071401010000c000660000c4200da14020000c40c0001c0007126600030541040b46101e014015203000040c40c1e4011311407100540c00f04181d18090108202d15240500c580d840e001c1582d40e480c1c00c907441210285c6007400400302c0c0880c684400c00080000c0e2a0980003046040c0c0da080000c1e10f8900411083c00aa52100709008501c0a000c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 849686537 1250 849685287 849685321
    0x60411120a080906040b19110d0c08030405150408030403090e070c20030136030935060406060b03010b040e060f0d05060703050c03040b181204060e120f060f 69
    0x3c1030300c40e4403090b00401c80d15180c40f82490b484000340040c023080a01d660041801700009026864070090400c0319925101e090304001c0c000e4441d400b60500510102941e440c01e81e07ca10b2117030305c0181c0e40c0e10341883d0103070103040d46802c202194a01c8004112809030400724080940341c00c4000d420901c1c041c0f03c00a014034610301001a09942480c2052403101042c107200284d6404a13103060440201c03d00c20507071209961000a000950812010400400f104580c034200440e8080410900300d01035850703034524004d0914542c0700354001c81c10001800360900c5690007508807400385619552502c01e0400440c01b4a000b040035085012010480b580e80d01e040506d03120b64040c1402a03210202d0a0140d2105c108491440102c1d04100000d10b880341c03104d0451784140d034000c40c181d915494000f14103900d03d1068250141611a076201004200400805000140001e43d926000345416100340b28a05e9201040c444541c0d00002180d031070048089841d660040341190005400ea5503405110800056 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 849687787 1250 849686537 849686549
    0x1050913050c300d02120f120112060e060c03070e0d140601030c060c0201021f0902150301090e0604120e0604032009011e03080a051b060411120a08090604 68
    0x10346401000d4024191214906501c801c070243c0d403c0c0c1c09a4610507102c3d041c4450000050300b15603496402000404007404003145030702051800d1410340c3c44801900103003a0080c200c00310901e1007401c10401b40340500210500d070f81000c1d210302d007013440003071200b40406000181031214540121001d03898088082c43d00c0e0b41c00064407803031181001e01c00b40d107640082c0030030344004400110200d2114011800d101040394180e00820420355008002c5605c0b9150a64100707240351562a50b00150740c901040e201d08400908180344e903540f4044407501200d0b940002c030b06160300803034108004180d20307104001a051550500b282c0c040b1400002407498451504001c00c030160b0820042c2c00c03440c900c0f1002510120607100e001640c0d0302c8031401d404456011003040a088041b90003840051000700280c410044a42012820214110105512041040e41c10340c01c0390700002c100024400501c5403c8152101071300da280341041e94040150302e8500088000d0b00401c8009448486500c03000116001440 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 849689037 1250 849687787 849687799
    0x406020903010b041d010b011d0108070306180e07120309090c051e07110d0b0a2703170f01120308040201021c0c17040f0e0a0b09041211010501050913050c 68
    0x503031010302020304509486094151f20b01000460203501400c24900002c18651385076080780544401110f03944d400900000406448010005991480014013600c0b03010f1400e0102d1130031f401d040d04600d051125480901c040e0101090000840d411800c10000d440140d140405d800c40c100c203040c0c1d0302d4403611210001401c02941d54103009a2040080c0440302d1041c1e60301c03c00c000c0003204001e481c05001c0070181800c04920045910801ca42d07008460b9000c50002043d4140d035103200010101aa07860290f010a03458414445401d0700301002641c0502044030584455040034004024541ca244009003889841e00100d400d41e8002c1200d0f490a411280d071074071582c016842c0051100e50500b07001c5844103c002c814000040101c02a04c0a9440ea00c0400318510300e0043e150402d22000b8001c109030940d144100381c065180c02000034803903030003a40c0704801500c980d000107185954030b50040d211a40741c44014010355403451243c90700116030382070481803d10181015400d14050030f0306180d12807 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 849690287 1250 849689037 849689051
    0x120313030606050f011d0d0b360a080a03020d18060c0206091009031b06140a0c0f0503041b0906050f01020106030c0e07020703050f03070212030a02060406020903010b04 74
    0x85940248442680d10690341482260b9940003800300c3c0c181c4001c181400308542c5100f80480d00c8040014080d008401440344101a03c00d07260080d2140d03065130300c100910612501c185451409100f042d010602210400443d40d2010000c03c0e02c4181c01d000040c403450000880300801403080d015140c2c18105a03a04011540303040d200e600c0303000030003c1c080300c401d400e03c000e203200140013240300c6100b084024090701059100160840c001c012140044007484094048a14a80c1880c1d20040ca4684221b40021720712a0030440c2c0003503024000c02c8080034505201c1c181d20440e80c00566100400c000341826901c039181e1b403a105000b0225465003241d080008240080c0040d8240c100d44101c450540300385914054540049080e242940406069500010000c02c100c00412002552020301c91060352102600ca0b80c2d0a82080400f103403403580c0c5d51001c5070800079860300e00c8901c1c41c40200200198078208401c40080c0d154034004001421055000c64026043c1e00e00b0340003410220304c010000c008038 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 849691537 1250 849690287 849690307
    0x303090907110d020a0212150f180111041d0106050a030f110c07030b07110307230f0609060f0118050c09030f21040302030703110103060f0810110f181203 68
    0x6514500d009070b00ca0701f0009600c28804c0004292810690310350300e04c040080c0d0740d1002c041e10140000d401c9000d01507480e1412100d0000c05e101d4454007106000090360303521300e4810050350080741c82001c241c00303541c140010800c0903000070486001d00045e04011495802c1360007010001e00c40c0b1141c1d407170724110008400340e8558001c0740c2c41e82528407400450015845010f0211251400c24212011550041103510f002c206450b00111b01c002c03c1da100c2d03888504440d000d2034102660042640303140c3c0d00c4607040c0b111340c610a0101c1d65200400c950101c1966141040d00b5480d9200011075030b800035903407004289a904d2820456410110182c1200c000310009140141d8034181c030118030881d805640c15598400280303404550850743c000b801003d282c0d0440d00c403c50211101d88c611070605a440381c4c00541c556101040d8001030005001030150b4030f129039100029190b000d8240315550030b01b080b20003603000580c0301b605d10b0001041c40f1055100142404125100c1c4c4090032900244404190700f120 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 849692787 1250 849691537 849691543
    0xb0f0d061b0813060b06040306021908070e10030c1106010b131e05150903010f09120314190608101b0c02060412021306030303020a1d0303090907110d02 67
    0x881ca14055240c00a4084104a61a601c141c0d40c5220415555074510701041464005003080030b00200036518140e52a6102c0703049070b100070150018044c3c40455100782540200c2c0e100d0b40a040c40c24141100d001d9040003d001040d1214840107041d03480d40b0800400d0310805c8000058980c1c40101e50040d42c48001d035183c01d82109100202c0010940e902058044000c2c0d2900d10440392010906001030608040011401080f080484410400c0c09140d130a030798240a001c20483e6108800200240b06007041c510905512280780141820458400c1803806110310080c0d00000e40841e91034140d035003404420280545901c41c0c01c10384500700c1050790f010810f900c5206041d11605d004034461071011010344840340c00d5080a54802c0062008102e03030900c80e09149000c5100811008600e1210340c41c15003100c80039041034000039404074254007040e03041144085440142148030f5103004141000950700d01c2101c459a00030002c0f00041020030703001d03441a1104442803c29036a04252600d00259 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 849694037 1250 849692787 849692801
    0xd05130203160f1409040b0714210109090c0b0c0f1b0315010315050403030e151b1312050319110610060804060b150703090f0504020a0804060b0f0d06 66
    0x108554202001a80c044c010320130210461028041c1e003140da4880c4c40321040485e00038650380c14405058440ca140700f6060006000704001183c04604400c0c81d54070f50600c0d0300f0160050582d0a02c1e2921140203d5030043d1702d40c0855a441001c40e90b50743e09000e949040c0109401d03844c400c2d10607031100c500b20449095800c070719000c00b81c0490b0f80c2801c98464058041d00c080c400542950310800350781c5d46419698002c142e0081c003e0401103291149442e84c20f180000c005865002420250284213082ca0310a05003a408020026210b003401400c441044150200d0720508000c0c9885000e14020804284181d039112040421366038041240d950300900907410034000c5110501a1310001001314568a1809064498507a00e150305a80d07595a04e400410413256055481034035881607100080d01e6400621120b882955107550003032038074180c8181d20009070401840f503030041c8107501c0d82c43d5010f41c0050340590420004100350a074007010440340b42401c400c02d03070003014102821050040c1500054 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 849695287 1250 849694037 849694049
    0x181b0d020910030c270b0c0d0906030e1513020612250c1101020f1f0b0612040f0611040b030708060a0501021f110d090203120f0d0513020316 62
    0x200b9590a1440450407150501a0300e404140c4210040c072001e80e4801900410000c0d40c0744482907142c0300c050fa001241c000d155841425401f00b0301d04010581e2080e040300007001c140c1000d20080c522030090a80342e0070000165801c8a151000040c07903042c5d6040820384140d00903080c15a510a540c1c01440d510b403003110034402d290020308010610144060300303030051002035526550600c280f5a24124000142c0620504620400822003c00c1209001070104034511922042c50031001c071240c901070700c04000c0444c2c842d100a001010481d4031039996183d2003075208003800d9858403540342c400000d2030289000da103240300c00f00700850103500460040d80100b0013a1180502a80d0b40000c10600000d00d004450060b00407201072004500c1c81c544194580341000e40c041134241445040c07204a4108103aa40328198032280010203500741485903442c100c1c084110689007000301c1100e0700c410704c50804c3c0040016a00d500007541d094400d008114501ea008054954000308030094900104441c0922 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 849696537 1250 849695287 849695299
    0x2b05010e010f1503110d0c0e1203310b0304050d0909020c0c0603220f0c0f08031603031b0c0c09090f1415090706030f0209181b0d0209 59
    0x11a42c080c0280d51241214004440c069480025070002c90240c82c1c0d42c0c003c1020304105000300c51002855000b1241c481501da03503900c551880060800c19881040c3c400002a03030030800207c600300c071040d00c001d034809500c4050302801c488001c40600060780030b1380c00421001c03004800d100c00c03c000410900702d4181a030fa21240503e445040342c0c0f0403480741049804082e4016000da1602c0c0c00e01401840d4052031a100e0b041081c40c50203c10038408548140c1243d0641c0ca0000303102c10010310707900100142c00400d00d4541d01070f003000102d903500d01c21082c3c0300c030200d07018245940816100703070840841102024030004074400800c0c00030785030201c507a50894100d140d401c004590b800f20743c440e51075820b80000e40400c52071995242c264200b00001403400c0c1e50300403c07101d0249032400c0748001c1d00840c62034000b01b205614016005040711121207035400d41034010000445603640d018002440e460110300c4030b9034070341c441d60300d0043c4000c90703c0400d009030360022602d440300c1c0c817956015244403801034443c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 849697787 1250 849696537 849696539
    0x6010f0504140402041505210114010806070c0501060f1203030b0f03102a081509010609061107050306010801060303080114010c12050909040c090e06010612022b05010e01 75
    0x708810750b0002c07034155400300d8490001401500d0190403001448002070100d080743d584460124045100034502c0c982e520034284401c1176441c40910903094141c4075403281420f99410300c1c100540b29100900f26604022081245605001d401e5004c000140418490303494550399070900c81c01c0c00b055032102900800d1401e0700030b01d0b5a041070186a449250014090800000b100d0740e030000400702c51003010994140540143c0056040c50000304148400361180030b014684014170401100b40b10141c0c2c0e0190101c0401000007641000110040d01c1e0507041c00f841e01079180c40d03464030300581680f0003685403240c1400024041c0045d030020040e42d01a550f910700507a00ca07490b80510310466028140051154454100815801c82c15602c00c080b180c94018644049034001410741c890a172425640402d8800040100f00d240384241b101c284040005815650301d4640701501c1c803031460790a03800c6aa00005c2039120940c1040300400030989051410b0382140315890480e0080009000360390f0056103243c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 849699037 1250 849697787 849697789
    0x40c0e1804030203031f05060c1e0a111c0b01030311010f06140d0f17040906080c131d06090319021b010c02042c0607030b0d0b071106070206010f05 65
    0xc0c0d862245805800031881c0d601c840c0810b50a0f880c629030076111000200304d0228040c0d503400c00800521000c1c80090201c00d001181c42c50400112051440d078035070001c4d07901c80c0043d03040000c501c10704904852074460241601c00311040744002d0b010040603840f00340c00100030160444006005206100700820400f112038000000300c807070f42e01030150030b4416829000460b151490030400150301c02c01d4070207415021503580700c441b80f20302940c500c0c040c500400d0610400342c0511401004144101c0100030102503d4045032102084582130110300351a05924101034102510500c03080e00701c02c04880c0c0c585420f44c0300d60740745d4204620442d020a00501703890460b910018100500a2000709084400c2103010010354007210a0001260815120100c520048800710813900c1ea0b0f291000c001c030072050401e5041814a80300400c5001410b1504955144d41d44687d4001c20803d68441403210f00c079100d8807405e641203e840300c440204e9204003803c0100c140d0b8080b07030f140c1c100d036200e51181344440e850314 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 849700287 1250 849699037 849699079
    0x30507050a0f0506152107031709010e10050306120c0a0305030702090a0509030a0804150501180608121e040b0307110f06190c030e070f0806010e01080a080a0509040c0e 74
    0x10407811751003001c180300d0703021b4480b5449441162240040031640d602e0398903901c600c0c50540145144a90960208409401d07503004100301020000031204440c81c1c0c007048002401c1808090704040c041c03620f564403054031000c104600d64118500071320442e00d56503a494501e98982c0141c2d400c0317010340712840c00701d20f81030700340c2c0034150240030003401641c24042c06032401c07520003100601c2940c200a00c820741102c940e8144c400c0c14068150150b50a0208550203d42001d40d4800d501ca8a9554170012070421000da80c00c1c1030755403038650707268012040c1c22100c84001482c0134a4100c404034442c000140000c540d00080c90034403040c5510240c82c910600c00a41c162504011210039420001c04280c4500006446d0320100c640713102c40c240000d802d400c041c480b0b0300e405100c2d00580048044041e0511501904200480c014080d281144d44158189002c1303540341c0e401c5610040500c400400c2c65010f142c002c41c103840031100054004c0242e0010040018040203c030b804460003412202c1c107036207070380d1500 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 849701537 1250 849700287 849700321
    0xc36081f061d07050d1407170c04120c15050c0601080d12090302011803120b060f07060209012c043207050c01090803060f01021501050607030507050a0f0506 69
    0x94a41401c00d41012110b100301c440024200404c20000708024003030b0306060b100c4e819400c281c20302c600060389006500900301c010b0030307841e01c16121814020407000442d040b044506440d2443c410b90596203413072400b800508040c1d00820640c0342c02d03003103104401364844007500484240300304840940e60f844030b019466000c0f0190410006001c11099004242c003500000780c110310a100006001031145880a0700c0034100700101d0002e0610004209141e05501640c064044201c80c0e0500c0c10301d059000e8001480b030070701d0082041e5000700f0f9150b49680140c00e442c603607108451a0540340d001d14000f50b188480b69070800351149191014510080b00c04400040e0021b004004c02c52007001e202e803001a410703400411200401004008040211000f800b9091071300c0c0c030660f10b00343c0747c4c01c1100400c80786038028251309045611200c220901018040e600904480341540c85507a030380510308040b213a9200c0c0b24800b42c4a8820b00c01030104120074a421202200c1c0180300744d42003520781002c40f95080c081 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 849702787 1250 849701537 849701549
    0xc0109080307081b0d12051503060115110f15010b0301120f020f030f102417010908070302030910140d1d06010e01030b0a0c36081f06 59
    0x41881801d00180465008104c0d00107071030700091000c0c15041c0190f01e0b091220802400080a42c0d60340056201a809440d4100e200c2c1500001c40e60000000b007580c40c8030500c9034030050b400700c0e20b80c28903480c01200201c82030038200e02582c1104003207011865503071840440c45d00c0c4120104000281d400594070607241a5031070400010b50003841c0303841e07040c00041e81001c00c0e43e101d60004030040c0141e42c100403078070441c08502c0143c0214604d42425404a60368080342040200c0c80401100c0020555600001501c8041c9141040000d8034000d803801800400310040107414005251020303d074000001d04407c24048620b0003070b0103040b000482d1000f403880b20b1126400c406004c1545102610340080c0c9070000c00c0300d160f602c441286c030380303581c58002c0a0380080b00240740c03480140180a000c1c40300651202c0035000500c80a26404002481503154480c45a04400ca4640003e0501117500b0940d241203c0854565009900c0c0d0449544411100d8040f5640030b50105410301d01198034000d840c2201c032b03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 849704037 1250 849702787 849702793
    0x2030405130b03160f0302040e191e17030a0c0c050319020c0901090207021008040f021509040501080102040f051206040b1308040602060711010e1c0c050708010b030c010908 76
    0x81455a20040c000c14002e4a81c540140b90121214805080011008149041440c580135145006020881d4000c031030075100d45c2c1001d641401e03568603003100401117503809012040890602402262003c1103201c005100c2210300842d03611002c10240614011148007001300b00e81c010043c0190307031010101100400da030704103000402550884480481c10120140155000d601001d00026a1a9806d801604044c0e0340400e0795019402d1001003a00444920b003000c101901b8291281d400e0171514503802403140310180c034413600e80340c0c42100760b07001d07171001070400d21031540c40d04071290103908075000700004420320600000d521718220b21861f40c3c03040c90394040c03d440c0d01c413a185c500c1d80800003458146600c200460000000718590004e000078601e036409010390741050103004060258003040700340e0903810308400066060b400304580c15070031065000b540c13080d18146002d4a500180308005401c0d0700840c0000141c00c3d2040d00301c007400143c120265012101d0603001518025958007540090782c0c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 849705287 1250 849704037 849704059
    0x20406050907020a06150e10080c1518040b04020307081602032701030b060c0307030f0509060a031a0a090b091303080f040204021e1b0303060f04051503060408130602030405 76
    0x3030000d9100d08103540c1b1070040b0001068a5495090007028150ba41c900d164030b1850b41004034007010701c804007105e4811582c00c45030180650b00c0c002d0b50300400d000301280c2803200c0c64400c0c403540e90b64001c0e43c00c200f0181040d9203d02e0f1490b809000034208840c900c6800710107100104543c0d20102c1100c80b04100a5841608004640c4003000368030b02c190360031418035907103079000101c5543c0c040142c0035000001c001550369046510740144400c0818800e20240041031000c1d040303640d911000d85030b4012580c9400103004106529020f280c40100c140d00d41c0000c109400894002115040308083c02002e44003071510340c441c0200850034020f505000f40005108001044c581c92040e10240c1d0458001400075040c441c00765058006088081940100200d00046101c41c614000c0b20908401c50300c04081d504525080011607011110300085070b00c219540ca00240380f090010592408489002e0203c82c224941458282455408030b21481161007296400244441c800030031282a00c0e40940181d26036 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 849706537 1250 849705287 849705293
    0xb030c030c030a08090301060806101a03160807030603080d0b0a1509030b0709051008070e0a0302090c0d110403080309100903021c0507050d020607090501022a0a0b1204020406050907020a 82
    0x740c104050340386d40b55490b4031000500840401c040c6004400c11800c00510602c1c01032185281343d0026480008103134248200f12100b903a1850b20a00e4081d14144400556a480d4080340280306680004004500c00308000c484400e40c2d81c05030401d03442c195040c48407a40c40b43d103003100c0d00d040481194001120741c0301c1400019031681409410609604200c40072075212400180c980340c1c918040e4000a25050800408551011104003915001d949010b04d6500b9900450750701a0028907280801400050082941c0440d070721181e1030301c40e440b14864407180c9038a05506103500565064080303219030040c0c0d0a00c0c2c03425114850185605070001e140120050090b00d8aa0103801d0482060107018003585000c15014021244c03410361560240c1054580200064020001303600240d0440d40482c0082078a082c0504d6603001d41c51080c0401d948012400700015540038182d040200c0e140800704503440761214000d03a0794040e501c2228140009500c400602c450480c0499040c3e0050344100903075404 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 849707787 1250 849706537 849706553
    0x609062d021504030f1b0b0f07110f03070623070f05210405060901090b0a02030402030a1209061e05030f04082209150807090e010f0c030b030c030c030a 67
    0x9540d9940103580c03460755070340e1540c81d9201c4212419000b02d912150803d00080e8000c82c3c0903810040c465a60580d00d4140d10f940c02900802400d00f03030702403914008212701e14001e810040300130401d40200d88540003204002e40c0c8981041a0440d105810a510800c0100c80c0a103040f1024050700d1507500d50303503528803040760403003070180e165002c2c031108004500d640e104001030203084100c030b4000c0c1215070030285001454510004c083c841c003a40f5003034410000034059882c81c3d4000c425440050b8807901d40d400024104030301c000005202a420050040c80700741c0104107002140c41d00d07283d031044141d01030a0403e0082030711281c8400a002040000c1c03c0c07504030701489030442e01030701450782051401403a02c65040348460100801070320550041280b000d040c0104a413100301c1350300003820b4516200c106030f92a07006001b1402c0315501c0d8000304942c05070960009015030020380c0c042c001142060f1000d00180118403c66009010b0303a00142058100050041d0181c00090001d09002c0c4141d150f08074 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 849709037 1250 849707787 849707867
    0x1205031c0f05010b2d3009070825060804060e0105130b130c0b0304050f012a02010b0a090207020a24020d0c050a0201050d0212040c060906 61
    0x421994503840c50070036807190b01c102070103840300c1140d444c4d807280d6610041c0c0c144440203000e802041c844440c4201c160030b40d102580d51403030909880003440c0c1c000084240642882460b9112082040810404ea883d80084c480c01126207541c29600d565170080048984440301c03100c0f100504070070520401000e03200700078850b8014040d040c00140700130740172007040c00e450341a9a0440c004240c030750300500784102080401c0d000200c419a00001c0c042c81c5c3d031042e044802c2403290b520b89120100005081c07140a01003c80e02c0c4521000030000a8401541603401000701200509045000c00007240309a00520401d2507013200140140046803038803000074007035401071300100d811204030303000001c02e0012000d041e1590281c0601118100c12000c0303000b846e05490368407020400801444c10750104101003411030721550207180a03952100c0f0b288085000c0c1c0708481c200e080c51191031003000144503500c2101d500b56a4542d8a410380190784100c2203c400a92801b0900c040c02e00303800c0030302144006c2d0a030705 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 849710287 1250 849709037 849709087
    0xa0f05030c16060b133c09050a0b13230f03120703050c0708071509020d030e1906020715031b212c07081608010501120503 54
    0x80c81d000c0c2000e1003807075800008808071101603d46409001c20b20380015140190754050000b080b0400181c6d0100c0f05656242c41040000d20201100303070000d081111149801000012080c4403001c030900e00145c1d51007186000f80d56005940e0042106c1c00451082c00b03e030150014803219001c210302141080c03400c58a080c0110345d12a42c04c0004001c40c06202074812004240198401c515001c10098241c5500030908001d84800700300740700004400e80190390b0003a4001c81058111103903505140000c14541d40702941c042c400c1d9448108240c0c0c064543d00110205441c50b80c18440065003030080a02c0d607001c0c030405604804c0040c000c0300c072101d500c0075801c10b4030300d0045a228107484c001c803100c0e00145008000a02103079403c8a5030110b001c028551440b43c200c042280c00d100780042d0034943c111518180b140031806030742c80354941c8100100f40191010750141c1c2ca04480d270032000b41400200b80301c0d407005942030000000c0d0b82c18410844500e8640c010016524048101c4440f00014501d8566a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 849711537 1250 849710287 849710311
    0x303061203040f0612182004020405041a1e0319061b08070201110a05030606090406030602160203060a09030e06220f06020c030d0e15040302040e010c090602030a0f0503 74
    0x1441d40300c0308500500138582c0b038540100d84500d4908070415035490603000d51201c83d41d1480b078800600641003091803031000d042d9540c0c500a041c000a0042d1085521550780b141c14030b441b11000480504032914a0142141c020120f070303c0790442c40e011400c1a2100b2075154004c1c008031070098040d85c450070b5038144204400109000c904d0b0b40d046244034602050000184450100101580c091090701c0b48048a14000c03420451540b50040c060300c00202410b00492010941100c95103494001e90003850344000e0540d1200d040e0079610302054215001644244640302c04501017441c244a0488401c1d015030341c00b48618002400c0c40b1f5141d200310388824410032462002c02411f04240000703400f6042e80c004080040b894688000d282c145c0040071107121380c221402e441d9002d07030844ac44044100341520030810000c8142c03203000030f5019560000e50443c0c2040c2d10340745640c5065102d1511809103403101da4159032030f404100c2c0c0d02e00420301702c031002c034900804a006a41c043c00c0035661050f050390781 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 849712787 1250 849711537 849711539
    0x20c040e121606020406020c090109270201030212090309010e0a0b19020a0b010803071a1510050f1317061902090a08030a0c030806010f0909050405120c1b090603030306120304 77
    0xf0002240e005510003401078210003048449841d000c00803500528801030103000303145021b0a04181c00c404418030788552290901d41800710390098068032405d2202e800e2004062620407140b0b52680d208540c00c50000d1102465045a46000c1c2f224100b5258040300300c50410125584c03200e01105220381690551048407031030300000e5907151105001c0c1070500041c40d1114028a0a203898401088075100b0b4044004c040194020040690b8101100c3c1190780072030740700140b1410b0b0703294450ba0314682110340001912410b104184d070056801c0b28428004050940a10619130307031510f500380c80e40303448000344220002c078080c2d4a802425032194003d0681c0c8419694011091031a4003050015002c41e8140300f0040916030042010f03540000f00782401d80e20201d008100806150b0380d80243c00742c40b56600089000c0c440c0030003c055001c07020f860010f85c0c0d56807144020b60743e0030104021600e4050b09542d01445400c1c007241072809003001800031415600d4180400040440d01840700b26148802d002c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 849714037 1250 849712787 849712793
    0xf060a091e0e04150f1b180b0f090f010c0213020c031306081f06090b0304170f19020706080112030c05031902070b0403030804170405041b020c040e1216 67
    0x90000d000c0c038420700d804095407401d41104c0d015a10222440c910184c9030100c3e82288a00c1800584910041e504e004035098400203480382090309107030080360b40080b0200703400c04c1e5001c810000b032007003032000c485090010118100444588850030f03c001c0d040034840703020350080c007440c0c2c000c2c0113010030380c0041da03041c00300401c203081d108400e03948490001900780080c17000442604120751081040300e03030128851821b0145c0075040c46440c1c440c05180c005d00000003400d204101c0c1c2160040c0b8000074200f580ca50011040c0000350b04900c101c81d40340d1841d1040351000701c0c000501e035801c41d50740351250b5105a10701000c50003185200141036044c801900d410200041c000d100410207036104161026900c81c800078000d01d00010750700b0000d464601000305102080d04041425405503004445010340c5c0031820b1088083e016903408150450f051500d40102c115403d04150380402d8994215600281e03101d0030130041d00d4003800380c4140c6800060500c041d0700f060500419100502d1000e4140004141e6 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 849715287 1250 849714037 849714059
    0xc030201060b1c0b030a02010206070f020a0606060903020a090e0c01050a030b03011d3021010303082e03170403020a09051012050304410f060a091e 65
    0x50b00d0030f0524140241c103003482000c41e105044c0300010980040100c50050f50001c0d5803804080c000f20288007103000104411482000401050f0f075025000303201141e601c00c800344c1640014042280309000c1010003003420b00252044034030840140004046d0000c001c8019a403030303030001d0795020030540c69207180c50030360320240a0501d580c11840c1d010f11440c1c02c0d0030300c0c0070300300f80c00b584020401441504115034007500c4070b10404500038402c0e10456032410303020350030400001c12500d10624804400000414103030442c103081e1180c00040c507629026000070a0849480e40b11aa039a0310101d846641800802c104941c2e40100710302680b00c2a01d00790304c90b00011860710351584641c1e0401c0c0c80d9400c000c0c2c011585070a1100a181603940d0000c16449507645a40700e0051f402601e0003005580000b918905400c481061400284950740004400d01070500102443d2400700c83c0c0901030011800c1442e0402c201211071481581d5503080043d41440d00ca106000008a83e0300c0410103070702c07c0070540711202 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 849716537 1250 849715287 849715297
    0x60d0501020318070803041413061a13090c0512100f090b1005040506040308070f150c0e012105151036120f050601080705121c0c030201060b 62
    0x8803400c00c029250f0381001c0351414074260010720003034005010400c40d03001d001440d4042074200700c413401c030000d442200d9140149520391228041d1481103021588120364040146411214200341440d120386404c50901a100021403042c006071040190542c0c12040980d400c1e00b00e110503101c0096281e031540b8100b000052070304111500e903a140021980e52a040182d100c481605050050401d0301e0840090210300992001030519100011000100710310b003280098441e900c604030000f0303940c9468503c0300a000001004004c92110340141040303601404a0b81c04503043d800310104020b0100d140000a084040e02c1150070004036514015030303580e1410850340b80b440998801c00301c031140d17003202c111912402c03945c0e0034141c90800a401e0181c40b2041e05000b51101c0300314821100f5454174040c000170700061005425405000e001084003280421404100c0700c08845501050b80401d240f9500d840c001c404d1040c581040c1013400f4060381c0234a10b480509030081c0000140d03541d407941484aa580a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 849717787 1250 849716537 849716551
    0x10f1d09150c0c0f011109060d020706020d1e0e06190e0607080f01170714010e04060b031009141501110a0302060a0c02030a0f1d0303190f02060717060d05010203 71
    0x1002c106010203c008000c14026070701064002e10502440c001e09583d144506a516806118001070012108501e0b40444a146030f00c50740455640c10940200402090485032004011884441c1250103c4550040040c0c1d0000140541090340b912501e004811450b0042d50f00c0c810b4940e401007004100a00055208a4141d241c0c0d480c0f914100b10b14900c40b081c16044811511400760005008090004482c1d043d140c1d00c00c09020400340520050b85c0d043d035200a80340d8464140703080400e0442a1001440c0108540d03180710701c5150302c0d43d0f40340007503804440b2481d03101d0000c0d4000034605441c10880d04001901818420815a070422055042440550341500564002d10900518044038800c1d06242c1501788003560402604240041040036851441410048405c0001c0041301807800080b1280c5402005c40365140c0a07110341110790200c00c03d08001003880c81038694540b90000c030310144076000359500d0030303c6480c10440050b51008060b0040b0340180c15001e010000400074802107002e808 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 849719037 1250 849717787 849717811
    0xb07020f0a080a0f0606121103010b03030f09060d09050615010f080915060102030c0106030b15010c0c2306040e1f060e120a050321010f1d0915 63
    0x511401403094004038644003a0290710000c104001556001c10244052603001c1e192502c403422909101e800342269421200021b8840c2c8906000c001c41c50001850440054000780300640300c0404040d12801080c1b40f035910030408000d01840d0b49010b1000700640a20a400000c0601040e10303a10700c4d045084a0042810000014640066800c10044442e407551450200440e00d080c075403040cac9502034190680900541c10000c18007682c028002c1c0d803890684a0000c11650f030b507905000074980c1e03041e0742d5444007181312105590594422010209002c3d082040030480610380081c0340161001040a0181c03a50034031a00d2040380c0c1c0d4440240014260000c010640307050001ca250f070803040d0418146100c89490300108000d5811180c60111a0000c548403905088440512403c10400e000014100d0100155903820b8a0b503c1000a001002c0c1e12241e92040e0b0300e0707551084c200209402080074004080c01400b0b801100000d500742e1000b4003009031400394101240800c0445404d03140e00502903 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 849720287 1250 849719037 849719047
    0x80d05071406011a0703030605100c1104020403030509011803060219020c03010e06060409030e1201020307260a020a031d010f0e0102040f05090405070b0c0703060b1e0108060f0603010b 81
    0x20490320307034800445401202616003540f41c401448136080100c0038800c011480401c800c410b1500951080c4000c01d000303020240d005207a400003e002800700072044440c290200c07945d1403642040c0c8295819281d060301ca103450030380c3c16401954480004892040052148000440015018006410540c0c50070b5200380c44018008400780c00e00c2072070b0500da030113a85804040e141007940000e0b099004201901c1c0040c4404060400715103070300d0080709094002802811003034201d501503004504c96156a40d9125401e04900a01ca012081c900500200c5400d100d0102e035410300d25034010007940c115418001861008610f59220f00c07000c100181d41165503031402090402d44038040e0b5038010088400031890311b410007140d9408a285802aa40204440c00000d81004810400700021b00840c0d42c1c0c040d1944900e5a1855580c800742c0400c0351217a0a00c04180c0c0e0500f0401420354400c8140b0517110360242a4500443c0c801c240201169805400214012403d4480c07000640c0a0300351048210740d14 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 849721537 1250 849720287 849720293
    0x408070f050f01030c080606030606220303080c03010b04060e0f2101050a02040305120f0c0601030b07020d0c05030a080a06050a12020a0f050303030705030601020705091f091a0118080d0507 83
    0x5034112504506140c05c0000309541e01c0d500140382580404202e882c26120740703e00d0040341c4e480c020740d18101000502d5020010540100e10010421030b4486c2d0380380842a50350a0310408140030078407550043c108180300900180c0e001e1222042d0040e800b4181c10001c504036000515013040c032099048064042080d5140307980021302610b42d12401c2c009040d450306181da6900f40c0da4011680c0000000180400d4450b400031408044a0b500e44e00ca03c101c44855840b404d0202c0f03041030039140000588281240c0d0f03541d0601600300c441c2240e401c440514104402c0744030030f603540900100800800c41d52200c0104007582d0f40203240300035140408007002c01e0803007803060080e202c0d0301d50400440140804010803013660300008803a403128242c503150380c4030380710b040060340781c00000d811a50784003040c44100403d041e0f02807003407040b0701708414042040c01d59840150381102c05152000c05281c11030b2401a0107940507110724030994800000601203565a115294284a034070110314001841c0000c004041c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 849722787 1250 849721537 849721549
    0xa0822060203040b0d0e011104081c02060609070c03090305100c23070f060e100b102f0709140103020a17100522050d09081b060f0408070f05 62
    0x1810150000318a01802c20184000c00d020701d0880540f1161500043c0074040029001070f5200c8141c1d1010319209c80c2c17688002502e8801203541c1e02d40c41820040a805818800034107107020307032070103461107000e43c642850848001440100c26030620001017000000034500308a40b9403080c1c0f21860004801ea00ea6000804111038401c0d003800b080e03107000707510110322038600480315006d070b001d0a4035403000410b2038040c010704098405d00c0002d004a11030700100802070b4020341110602201e150000106070034080c1c815a05841d441060074008810705044d0407a0038140b0b031365080b41001140c445076a6896681c06540c00c40841c000784440d52001003045007080301c0000060440440320ba803201b405e00c42c0c016901d801c8440d0f0b0764952034444e0f01003120b002046c070131819007001c0d0843c1e084031800700d820495034038142a03402400040d0400400541c102001ca206150349880b15200408070405004100040e0481000c85072010420080050911010002007000f040361040e080c14041c904820004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 849724037 1250 849722787 849722789
    0xa0b060312030103171303050d030b13090506060418050307111f0f0309060b1804020a050f0607021201021b070608010e06060318120a08090f0703080313050a0822 71
    0x45550301c00e200500004e03131000030a004d4000255412510385103907403140d00c42412290710240140c002e800244100075415003011282c914141c0f01080410640e448540c00c544446001501075084440456640d2a05820842c010110344211101d6004192116030640d030088004496146080b05161001c0c100000301a01c404400100e55151040d455806888609001030b2142010781e20185d000810009074044014114054208000010010300713403c03040600344c2d400d92144001820016152034010044080240c2c080d00090400c0d0300c5a09104187c800c00540307500a540902620702c0b400c8800c010303c095000301e2801480350318508403001d040f803001a00041143d4005204025545e2204000c82c1d03008000c1c04d041c4c480e44144080d0483c00c1541c56000b95483c0f40c0c0c0001c2c0d42e260b079a07004809900038031240080d00d003409401c11266a035080f032403000a10020084c00040c46039a646920707030841078081c6007519040d401942d24101a5400555041408901d07401c803081242c02895942c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 849725287 1250 849724037 849724063
    0xb150c010b180103030c15020a080a1d07050d020a090e0a060b03010c0c0803040606090c0203040501030f18081b01020d09030e01170105060c21120a15090b03010e0a0b0603 75
    0x6406604450140d030b285410500000d0140070100440c1d0301003180d0000319400080e0b134421704540303415400100515030041030b0b41c440c2409080103907140d0980c400e0500070544409010050000c58a014103000c160701d171110060382d01090088001440da100f41c001c40384a000a07001511a0310b000c0d190810403206252039480c02680340414800b001a003148400c10301540020009859640d545846005440142c00a0f545603080c42134142c0001c1d0004040c200344c0d84262400e2241c007105900e9001120b01c49c032080e1310781104841d00c00f008030b10108010480b40100080c0c10b1041d07040d816019007039074421524004155a10040740003410b41c0201c10200b00c810034030b01030040450b002842614040c0600445225010014041907000c204001142a1800c410200b540402501c0f001701c0e0141c005400408910104100054039815a0310a5504800f103841c1003204882c00c0441c0b44000b40b84c04903140c0c0d00b5643e214480c4151801c00c20440440f43d01c2004905810720f02242450f0410580c80c082c8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 849726537 1250 849725287 849725299
    0x131b0804020915030319021c1809020a050d020301031101030f0b0306161b050a0c061407080a27050f030c1e15070303150501090302030c0907030b150c010b 68
    0x100c4010782d01c0c00841900321a07007404524203500c0c640002402d5100d11007503200c0401a49400b00d400350740209242001c8005644240d0f007a00b048a030650300e0708000c541840b1401000d070014800000c042c0d0281100352001d02c0c1c40741c00d1078101400c6034101c2e0b1080c0c0069036440c0c5407408010b044c1da814080c0340c803074000d849000c0c0010480d0002182c1d840a010742800101c404144002840912503103403826140170665030411480e03240d0030010b0300c1d0040c000e4103076188101040c001c0355640c02038010044044c2c5000c007040c50310046448540043d04106a110300300700200704055408074070202c0d43c8800c0c00440c07010181140c80d103820802d494240d80c40850094010300c8a4103959901c01014414248040014024010362040020a001d40e640900c410003640803c480c4141641544121000d109500340300401c181c0ba0001507449801c280300c000c0d4540c1c049055202c2e242465062140c11000741c1c00c01245001e8002d0001b40030748600410700140c40004a410702e0842d10034040c2c5d21803180c0503950 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 849727787 1250 849726537 849726541
    0x9010303230403080904050606130303050d111908072303090c0a0f090f0b040501080a0516321011070504020f090d0f06050f0123060a030f020405131b08 67
    0x42d40c4103409501c9140d1b2040f03580314002015503e07488210780669100b46018600c450720380c60064181d80001c00c54000700e601e010040b00310044000c003100ca001800b0902000009403240017250b13110300040088007005400041d501c0822402d503a12030021040d40b425a403640741669485142c0910000418030400c244101040407480c1d60189900303444541b40081038050880c840c3c003018050501c2ca43d40c006250000006035104041901d100482c41782c0269004a410700c8010030018056000c2d024003482c1c6810321034545a0303068203590f041006548045001b90740003001441d0f026000c1040b0000c5266508a00e081007030078409680a070108503821410032005880150160040d8500a401402c2c1000003009204041c41070b0a60180d00940500184c68070243c2801d01800038801d600c00d03045074100f03035900304030b084200450b0100301078081c0e400c2801c840021000f0301240b0741c008464941c00c01c4003040e03646410302d1110b6103002011000c610084805000e665960000984800304500001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 849729037 1250 849727787 849727793
    0x30309110d0308151f080103140a110d03231e030f0402060c0f0118060c050a020d0302130f0308031b1e0306040f090f05060106020a0c210209010303230403 68
    0x4101c0c0d00814001190700c1010102004211012513000c00450506040881c5d002c1c22a80401950b0589200d4400d02840644446050390707603d080820050182c10a483d4815013420843c210a01443c041d140c0410980c40742c00c521895400c1c2503c00e540c580a00007100b2440c41e11403510030140c0344805400741c1c0f442c98042c5c202240810042c0009100e40c20001d03114104240802c55079546c01010402041010307005c4005090b07030400e01c0d404035000ca08000d003000d0191302910640310380c44440e170058414a04a090220300032341c404000b2800451000307001158420702d091049019500c00c00c1349507524140030442200c00424155070030244981080707082c01e0030902c3c41c10446c01080d40030b10700740c880d155000083c010380801c00710120420f00d018104001c2c00701103075a10141c1c5004030705880480e41c0303505040b82ca0b4a480c01c40a050314a100000f0001504094000e2000340560000003060048980c0042c20700341082e4810340000301c079131440e4180c82e10b01c014280509150942698a0185555 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 849730287 1250 849729037 849729047
    0x9180b1503041a241507170a021606020d120e03070f0606120206070609051002070f02011101051e060307150206010603050c0304032106210303050a02070c0b18030a030309110d03 78
    0x105260b8000e8541200720b810b401c14145c2590320159002c104808012103031802079007150802e0203000018415010780085d120720090790b64003543e40b40d5001c1c01e20203040140c10760f542210700b010f464140d980c41c0c20321180408240003a2010130310400d0040383e10303a164103019007941c849030415856142c800d4405c134011385c1d9400c00c880c040b6078040e8021803c08240d0500c00d0800402d01c000c0007407a800080c1c0001023040b100340742d810140c400d80394455082e02440d07802d0300300c4608071421079000c41000382c1c5100282c4018825175010100804a4007455211450042030350301d00d07409030300507030f00c100011300200e601405201c0c0d100c1c420601540c2149401d0320024044c421001c02004600201201103080c0358103a000ba178054411030043c49070385900e04601c0d440304009100241d00080c605004175041604078000c407a5800e40041c20030800500381610b40d407050b806880c2080d00110359010303c0000d900c06202039440c0714000c0e18005010103150509408504840320714920a0313228112200c0026004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 849731537 1250 849730287 849730351
    0x7031a0f01090e09250302091807121407090219140304020f010201092301060b0301080a020613090f020418021c180209010f06030c09180b1503041a 65
    0xc0b03c4069940d1914040641008011581d0031960300240300c4600890315440c42d813404482c400da03614049a84d552042d600154045280002c06810003007041084400a85594807007030f01a2044414014492010a03d400035980c88035001c19004500440c0704112001080d2040a0364103021903078003601403030142a440000d0000744191006601495507074404d500080200703038410307070500326840e18040210700e1904240854009600303014010440b10320050599040300c424100030500300303030a43d08010061300003400020744000a144c0000704250300d0701480c030f0444041000140e655082410542810580b000e003000d24600406c5024031005a402840030705081001000603403041c1c07440c21184403802076a0113984081e400c000442c41c62000c0c05182c1c22110651030811042840000c25a1624464030980312a1901c1031a800e01d0b513009600107150008000300090341002d4018100b28150b00b09603410348000b4088190703926403d510121198004c002d440c0c4000e101c0b00c00308503c0d03001040c4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 849732787 1250 849731537 849731549
    0x90203210a20010e100c0f02060a05092a010e0609010512070917061e07050703081003120305040b0705030c07031101090c060f0f03060605030117100507031a0f0109 72
    0x51000348034000549900142c00b042000802440f12201c5910450303074400e103860344410290714014103604068040c0017125074080c201e402a2a140da10104210000d08006049800a00410245d620982000f0048001214240c0003401102010030001050105007880c45809140100b200e200302da030f00b00c005d440140c0e0000d001160250baa071403084400b20031a41c00b124040a4a181c900103200e801f00d900c62050001d0340d80d4210342ca51820508c001040241c9003032011030810403046c0080303481454803075481b820580c011410150359a40d10400c2881d01e200540c0040d1341e030002e103c10070055440d0300f0313040b40c554a0a0703070031420048110321a038401c40600074140001140b84c40709210003234112821035504403002058641d96041f026107080680c4d80c1c50300c0080e4290300c5500300c0c0c501a1007403100743e031240e98481e420f44e800e0030090300404103180140b07003880c400c80150440d40c1402c0c0c050f03988234207055940802c52030203941184040510a101640c850084824807500d980da1001e802800c40c0c0c1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 849734037 1250 849732787 849732797
    0x6060903010e0303100915030b061201060e0c031e010303020304090c12020c01020c2505010807050702212803050a0516050d140306100f1103030a090203210a 69
    0x815100003a00405401440e11041d0202208000f600c0c181c5140e0f001c1242c50050080c410b000c03000e0745100c00301340d81c1d00001741500703940c102154403414000d441080342d000c04000040d60f00d446041011084804655120305003070000100325408040c5403107218034020300d0266902c65415680c001c1e499028601640024035030300e0401c1c1130303900e1040c0080c0c0900c0801400071980c1c0e12034040c185010350b00030314000c2440e2140c07080688030907112081c13859190710b104880000541c2444011100b80001820345010854140080b001694847c0d2a00c9003411039100600c805540030480c242c00c082a40c6205480707480f114040044c441180b100000159906280169498503511404d9a50b4000d1034840c4034000e001c440e596042000008141c0134102040c0c80340c04000050f40c030b89401d40e10003240c0e001c0c1c00444440c10680006c0c0074a00c80f503000700c400d0403c10180c81100170071078695041115074540752070300c0c0d41954081d802c0611041011840044600d600700805242d207407200e20030107110b901000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 849735287 1250 849734037 849734047
    0x90506010501030f020f1b060f0f0606031504050a050f01051c110d0f03080603072301120e0102391209040b1f27090e010609060e19060b030606 63
    0x130308550440300c000508400c400c0d00d61400341e02440000e44004402d4010340700d420085200d0100c603e108900c1844002d007100c0441e070340c1c00c05200454101410007441a1544908104c00340d896006840c40351a8683c400501c40c502564a4110000181c1c1f08600880c07034a4445180f0380c6007502071060050300201c0800d881342204010620424840201400c4054040e480c4000c0690101c040d5001e00001c400302c07118213449803200c482ea0045a800d080e550030800040c0030840d4016507480005641d041c00000e803d00c0015181426a880048001c0760380c0c020b03000300c40340909102c81040071980c400f00d80991980d0941c10443d500c0c407005401c105603840100d202072855071341d41c004605a65004d061001a285e54003107039104013080c68040303c0401c518811100080c420b0401940c14091441010901035140503101c42c020303d04880030040a5480790342c00300c0c07011441e0103048028040046010400e141c00d22000e849284c01701e0105081c1130400b50704020441200301038a41191040f43c5441d569 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 849736537 1250 849735287 849735311
    0x10e0307030203060c1806040506040501081e1906080309010e0913020307030c180b010e060f0c12040303170709030308060102100507080114090408030103060504080f07050d030f09050601050103 85
    0x80520340e440258103109030820410040000405890b40c88039141c80301158001c40c0303007000b209000e5402107a03003050b018070040046d984110512900248500c1005508580c80000e03056030002c200c0310b4040c90701c00458a0300d80c01e4268030a4000810480c40510306280c0703414002002c15240c10714807441000d40e000070542c5460300e07441800e10036a009048400195032403030302c100c00700341030700c03800d11000c4c000908682400700d40d004664a114059503044002000c030310400400360002c107400034055805100303600310100104407001441141c00d0196885605c0e500d0020407542d444070100d010f05031250240000c040d0005445001c1e01d60604010085684080040341b41c40b40381043c401010742090244006240c00c0301603141650355540030104000285003e014250380240c0780240100d10800c0100082030003a03001720f420a124480b0945000340034151440550003041060752140c0001681a00d200d8044c0b16501e2040080b0400f40901541d5803201030f01c901051091a062684411402c209 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 849737787 1250 849736537 849736543
    0x507110d14240601050c1f0617101104030c0b09010e0316030b060d0b010e06060c060f010e010504061214011803050c100513080702040219080402030d1409010e03 71
    0x7a9014100403200c0701c0d25092020b40c201440c18030b00520a403107a1000c14155407007901140c40c04070121000748181344403283c0f90b85102d0340000610b40c100d555440007103941104030302c9848070403402d507000b007026a107031103d6907081350003902454034444810801040003c0581860808441510f030800c1e888107100401030701d80c2a0506045a4140101e9072072410320030f00c580c0000240c82c000e0340c1401c00b03541c51500388409020500e102a000500113030041082e0b118200029030302030000303842142410542c0c41420301e00001078810914003030000005006111780303080c0081c01031074101d4003802a0343c0340c40c02d600c0c5078070903008000d03000d0070031b1815550413008250030080070450369445000f4040741500340240180c102894170892801003660a5410303510b9401460302400007102c01c0c040c0302c07645560341003040e804000101e8019400740030560f03100070701c440400901d0641c1c3e11100c0312847d2901c109030510300c011540100f401445440201c001c0f113142c0a841c6003050a0914051000240300040d00d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 849739037 1250 849737787 849737813
    0x4021302030103060f06050301022d190504080606030109080f0a3b09010302031e070f0603061d04050c010c020d0206070f03020d030e0303061e0d0606150507110d 71
    0x950180000000003c0220f2503004c15004c10a4071003c001703803600e40040509078442c00c0c0e41c10b9070402c2001d0040284c514241c080c660a046148c3e0010b14050001300c101410581d8a110417010940200741041400c0080c840e03164080411002084007500a65400d6a94007074082034156045c8003141101c0c015020b9184e0120540a00c4414106440406910b2501540d401c5401c4007680c03240240301c0303d0741041c03464507068036401400b4007084c4003000c40c000810810000c9500343c03841017080000e81d005980d13118001809141d90041103041c00c0460140100c10807214007a100d01d880f0b010480070520100b80c100d940e00091a18184880c0c40740000383d03d00c1814113000e5489103002491004100680e00c40d501940c0c4603400b9100206000c400c2542180d80a1a644180d600704100083c124039009041099840c01030401071411809030011a4866140711000c43d00e041d40c810080c04182d205191100504c9840d2500f24504500c682e9950200506910194011700035400710380c040000c0000200 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 849740287 1250 849739037 849739069
    0x60d05070507020a080c01030609020f0301060807180603231017010e03031009060510170403050706050f04022d040216051b181e070915020a050d090614030402 70
    0x510145d110086541c8074120303618124046450032a000a100b01503002740c42050b00c2c8103d0301410350386040c42c1a038000301c001742848104089140516004041c1c0300c0c0c840d020f050903036400114046105400090b0101038030314082010100c4003000018a103140350a0191880c1030403a2882d003208145c91805040e04950301c1c8100c1c08080200304d07203c024504030500700e4403050340910400c0c0c0c4d290309000c0d0b801391011600c000100c501c045422603045811406411911a01d00507141080c1910346031300300e4006555015401d0354580a11003546428108400130020308003190789003038640c80d2032130200c1d881d046200303024039008160f265806260100e000502c4d0b400c1401e40e211400b40c00700d03004d182401e000d100c81c4600e110030240d141d600c101888061150780c9600c0c0c0144d240034030808030512103034018404810059200c40100399000348a1110748010580d800800811000e8030704541000ca190302c0310802c12413040820401386074401800d001c030341c1e500381d9035540d03980b55030001c1090030001d04881 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 849741537 1250 849740287 849740299
    0x203210906120a060b040503150714070f03030e0c0d0b06151201091107020a060e030c210712020108011230020f070e0105130209031606020f0309060d0507050702 71
    0x400344403907151a00030f10804002c2c50411600b40c07201c194107000d0160b0f0203103a8155014883c000c0000040b5000c03650040701d40e0a0030042285080c09401040d44010021504003007010401020107425009050b0300c0c58003a0050aa61840100403c125040d10742001d400100f4800101e486619412401405455802c09495030790032400d401d215180000e1084800e410b00e407981c51010548800103072017036590b00801170b1611500c1c02074121500030b6164802581401040944522640c0d1007600440120102c8102e6049910302ea079018240480d82c1e0058104880060005005030b03071010255042d10300071154031402c900d2b28180200107805128655145558401034560000500e0607080900c000540c01c1b500d58130b4014240c0d40d111010391182d24035070603155005100d0f0b490007010b103004400c07120030014141101140000d117040d501c01040610403031040414006035505002c28007080080d0401545460303010404660030b0302c200c07141003010a0b59100807a030310900c540308691503103800902d8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 849742787 1250 849741537 849741547
    0x80d05040605060924040b1804030306051207050303033904172a040905010f090c05060c060a02280305072703080703140408030901030f090203210906 66
    0x11003002402e0654910344120703110030001d800d1314650911080028140c8001102200351141440007901050aa440c1d218102e0001008209200424035205900a64000c42d40f94644010301601c100c0001038487e05801c05001444941c5001044a400c800b94114084600c8da604000d08a01002c04098403030415807600c2d001030f000070b0b0201800564035040010f940151519404940d81d0303240c00700c2d0714011040c0980303424640400051114050300043c1011075400d41f103966550840f400009010059aa035541140501c40305e8140c54015203010384510b41351066100d03015a642e0130041a840c010390300000c007082812011404032070b041c218418001006d03000c005020700074000850f0300e180060060304614104408400198000d80110024500d40d10b0440e103c00c038003940a20415414440390b59808800384015800510080c1100da000d1501c03a40140001803c0d214544021900c1c0c908102803900582d401188905035484c4000f10f11500e10795107084940c25018041d50309500001c0032813 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 849744037 1250 849742787 849742793
    0x20901080307050c06270411040611010e0313030b0402180103061a0102010b060405060f1615050c03102601020a0e01020609060f04120311041203080f150d080d0504 72
    0x400340c10082c0c400c80544400182d54400d1140da0f0080481b000c1e90044d9058042e58403c90040f90316031088070150012034010441c0d6421041644a640118005081d045807403c140c00d0a2107070702880e0202e24081c1d40b800301c002c0080c41000801e40400b420181d1610003003801c560354001201c00283c184004000d4640e903a0804000800c455612180140003041103030b4031640c1306104420090b100182030a0605090009221458224044503c0c002c0b0b402c201c422280c101140300035800e54800c00b40d01074400012030b0b00c44103450b07001c0c1001034a242d0074014000c195204961481c261580f0505003042c2103140300c42609012a40c100c40b41155100040861803142c0c040d030101080f0740c080c0c080350300c15120100f5a640e0b95008503001301c80c915200c004140040d55241d65400b80c445641303030208200303000458411156102d40d10000f685560625201d0030190400340300c42d40b049401011744290f00d0090180d5030407034040380c0b000344510031b07400301c5900f08208401070303c026652084042007540fa1503e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 849745287 1250 849744037 849744043
    0x19180503060c0a1211030a02180a0b1e040503060711150f061518040209010c05060f04030f0c0c17070b0c07090605032a063703020f0f1602090108 64
    0x3e56000c000801860855660300250b02499070040a401e1480d407942d680d0003020402034001d0000101c0601d114981100c0d40d5982e0045607004e02040510956101d82c03440c2120400c00c231400062900c2c04081c0000c1200350780110360f0a51045860a103d2526000345075002c4c2002040303440401c81040360401d026446815060b007078800d00c402e40384201542c400180192560181900000f01102c51030346403038050401c1d030041c4c2024541030420700803a600380d43d10a41458022104c02524001c0407041000789907100d080511000100e0500403010350090b100c243e090780e151700640c0405490066814001c11003086000014090124025111200240080e4a070545e620803004442d05048001c211072401140d9850f440180c142307469070461106130510000501000c1055004d08240524031354100c1d0b00c100b80d4142c407040d82c45103043c01c024440b0181c00e013507050010720030184140000d541c00710500342203403407400f115000c06469890340002d070450700740d031103c0c000d40245140000103000d030400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 849746537 1250 849745287 849745297
    0x70504170a02100912060207051609050a0b0d0209040303200403031101060803040b340609050706110703031b0c06020f0c0f09060405450319180503060c 67
    0x3183d5009920814a0b4111618800390107140030400750003801000041c480c0d40203010a1b0302c0b500640301140904000c82000260340d502105140d43c03141c08000d1401d016100b024031880d800c5902840d500c1043e000710780765110040004043c15541d0100fa04810780300c90b04a000b10f0080c6241e65640d030344910300142681e5140b040280d456090080105001c00080181c505032403510320310038148103038003403001d0900750b4418804103a040400464112200c206000e4038280b4043d040c0031545102a291243c50182e15900080411030f42d0305460400c03010120303900c403c8a1701840c24003156030801510041501040b4802449000503c0c0002191a00420819219900003003602c040c18903c5060108040e414100140e0180b00000080d0117840c0991020380c00c0100c1001d00c08000705c02444a08060840c1180164600f41c00c0030401000c40c082c0e00b02590303466015010b14104040d280e042c0c541c6006200344101030142005034904180742c0b80310010000d1100070122902810103801400302a408 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 849747787 1250 849746537 849746539
    0xc17030901021006050d0201120b04090305070b07030606120f14100602060127181b090b15091216030b150102160b091201060f050301050f070c02010503070504170a02 73
    0x150000506018201e481010105c03070003d0139a0b083c0012a500441d480700f4440020403a00f42c2d01d846004c680d86462103288140385c400d0f12503590342c5100381072201400100918101c20107080080038030645600c403408042c003d8041c48041032620a000c1c20b84040e220340d41c50508035414000420404420522a800480b2010b40999000e6625180c00051310301d038500b001c2c071614041c201e0440001094bd4810b0803034282040e000800321440c0da031640c0c1108031066400740b5a0000c4c81c81030009920078820055403450071581c00c01c000503510b09801c010301484013014480e1201c000e401c503003040b042c0718031150941c008803001c40494483c40e00b40704014060f25081e4000e07411800e920465400001d040c0c0d0320445006030109903600c1c0a141d85055404002d0035a0440f1421403410440074090003218058210401e81c811050305000034142154002440e040480c100d10381404406600501c8010b00540c0a190482d520358030742005607410300c295441866802101281101003d07030100d03511070070502c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 849749037 1250 849747787 849747793
    0x4020c1e070b072006030421030c12050606040b0a02070312080106050d0e0c0a0326040b030f0a1d0606010905010815010c0c0905010b0301061b1a040c1703090102 71
    0x14084509a540c1d00140203078031503000700b00800d001041d10b2402a8403a5032031203881042c024481e0010854980056078101c5050440300802c1d6000c142c00f500070100c162062030104040c0b600a88000e041048080e8010300c000e50b2600440c043e621000112001780036810109070f901e4815510096031011140b000b0359042098a9050030100d1041100764102d508980c1d4031420001d40003003040c024001d554160200d8400c0030000d00ca551a801016001107001300404140b010170f6065074000c00b41113001c4c40351401d00400051060002000c1902e4102c0c2841d0304c0340003980e1b1024000e100410380032102c0103840102401005415000140441c892002a40ca80322165602d80042d2000b0310140d0b02444400315000c3c3c3c6581e15442000800c607468001c0194800c0380d07641c3d00d4207504840d400e8120a0f01d00c40000010b0202a801c00f600303441010340c1035000c50480f00962550003009017039082121080c0310a4000c942440317200d980b0b13030010300210450040381c1d18209000590741c0c4d01014a290141c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 849750287 1250 849749037 849749083
    0x20312040308040f0b07080d021b120409060f0815070c170c0c0409030503011e170715050405010801030204111c0b030c040911060a1106010b2a0d03050c04030204020c 73
    0x1140b100e0a0790f001e980d12086aa08045076503035018041d4200ac022840710710440e400c0700704035410800c46404540c4840e149150f076203007804c0c1040300f910620b80103040034440341b600800c681800003c0d01e0305034110800c003848a5484400d002c071054006a08090900942117901c1d801c800c1d6003000070490740f20282c040f40c0c0351180c05400c2c003003600d856203009404104240010450100d84440c2d110964030300e00102c010f61510340600c461350380000c80746c11360103510510041c0710ba80309140450b1480742c6c01e81040c80c1481d1802c00000c7c001001400024001c50322450441d039858138000c151007081c0c0742d51100301d03810301c5658112401444d081c04201d100340304400c3c41060906051180c50081500200d82081c00050a002c0c0000c9900c540d40c128100b0051200780100c6c400c0602070716000e0010070402960300e0310010781100c1102c26900250701c030b000b40410b04020742c4000141d03400341c12100741004036207030342c0b008980c00b0540500d40c0081e41040c000119603180c003601003181c180c03042c42402c0101d02c035 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 849751537 1250 849750287 849750299
    0x150109050402010e09071b110a08070e0a02090607020616030e04060b0d0203041106040303030606080a05071d030f0a06050402040f05070504030b0c09180a051609060c020312040308040f 81
    0x6500e041d00d001c0d01040902c482d02c03210b402c0c116030b085d602ca142801c0442010200e100c0d415002c03004881c05840c00344070a2a855980d280c025640b40040c0204002016070b0b81c108000c00d03039803980c050940d0044507800140201d00b911500107980c4095002000d07079458000ba8003000c858070380140012400101e11100001051a240c80356509a070007c2c01c6c050704004909880400030352010300195032244c00310f11184c6983c0d50344070003040650320036134012954070318140001c0d113840805000c1c0c4107154100000c02c8117140d0f01c85900004032440041c0c0d026040c1d0041c0c082804c0c014541407503509401540e110205100ca42d40086018601c2a0790802080382c0543c100e0003102c2d0140c03000030014804200400c08942804d481315001002c10500701d180c5010b1070b00080200140c204810900100d03841044401c1701244289580100000d640e40d51196802500a0610829004440910509500078400e546041189910003100125819551500c038100403140350094410031721610000f040100304 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 849752787 1250 849751537 849751541
    0x90906050a02032208040f030503040e070804020f010f2001020a090909020916030f05040303091b150c060207060e0307020307091a13020d0630050d0c15020c150109 72
    0x4201d0541021500e604118201d60010501c4d41c034045d644204180b10206844405101260003035204100940c0d40b0340c0b80082102ca40c0303070000d000a040c0100d20081001680f1a400e940285da08246030802451500040655219040b040121411200e16842c0050000c055000b051705d445140c50b5001074995607105001990a507100007034011502c02d010a401d007031b841e0310242c01c0780010306001c030310000300e1201d00007190350450341500003940702c0c646801804440d9801085650000104c000c2d00c505001c0c1e28580000d004113814100860141850184072a40c1c0c1030304c0350150b010b403051040c01760f980d645666a030488c02042c3c0c401d009580c40011501c0840c03152511102005520f0306c4c0600764003003040098454052129021602080141095002845004050b1401c002101e07102c50101806a00b0100003070104078948014030302c40741c0030510000d2414004c0300103150038026400300d850300810080c3c01001c44c00c500c80c00480c881c4401c01c00440c040d440720507800f01c0141e5980c0d81d2825803003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 849754037 1250 849752787 849752791
    0x50406021e0703030f0c17040911031006080c07050a0b011406131e0503010906141509150a1e05013e030c07032405250e0604090906050a0203 62
    0x15040d4050b802c100000790050440c0b050700c44950416068a120980f11403802203a00e10b4007010070a00040c05105d500c1841c411500c050100712025070443c82d040b4401001c0040394054001401400000a5034500305401200c5070b0550141c2030b54007103507041ca41009165000e0061820032141c0c0d6855907210f040840c00d94240d40c20680151011328038210070481d2181f81042e8803410000c02080201d042d44090041040c9a0704c183c500050fa2181c0c0524038110040140c0320009181c100442c3c0c500c555100103009400c2200c032050b0480d29149200084c140c1c505c250300500940000c07030f084910340740140210400310381084e00e07143e0b03c400f0558400812042c4103009a40d44160156980541d031186041c400c5088003801c007100c0c60662040130080c0340940c0e980c801c440c1c1100b0f498044800040801401d210f104400c1804c0c489400c184000400b18481e81c2c1c0902d60a14030341c50011180c40c071030103140182003801b0700702c0d96540762520b050502a0048541c240c4482e4207220100d01e520040d40b003224 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 849755287 1250 849754037 849754093
    0x1221010b0f03070e010c0b010e0702061501020d1b060905030a02010f050f070e0d140c0a0e010602070b0f0906070f050d0f050a050c120a03140c0720060c0a0305040602 73
    0x2c0c659076a4034001e54441c482c0300b01e164100034030380145d0400108110300d1107010341130101c1082c803103162180d8000d1814400611403241c80c00d0046100c0074990700001c00c008906c02c207050030314103400000f03107510001710804005080c0313070b0038032b2411402c1c400c0c048000c0c0b00002c00c43c0d000307110a425280024081e9002034850140c3c60301c0202c0003480c2c183c402c920041c00c40c68000e1105d84a140d040d00e8000003800080d400c403101c3d4015501940b158a01300071414005e01503030301078003643c1d0300d4240081e4885000d8855500351403800602d58140300300620843d5030941e40180143cbc5c5034195400e01d200080c1ea400400c076102d2061141d55010310b8010000c1c1342c0101050782e074492a15403014002c07141038000044440fa14400c100d4080858442c1c01c0181c01d28400f55900010b00301c030709800c01d5020300070281504003810000c02c11070012a48840101900c400780079520041c49001d00040381091003000030140303590140c9a9408200b551050040007288d80740c0d0308807000c1d6510100c241000d40c00f455028 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 849756537 1250 849755287 849755317
    0x5010c030c0936021308010509070504200f040305011103060109080102070b220b01080a0b010f080c061804090f050d030b2b05030307080a0c03020a0203070f051221010b 74
    0x5016810030403261015510f8800b04050709180400c600840c00300d00b03982085650f83d444808000f000302081002000801c070481e81031141690890100c4400c0c604c1c03044440e00d082002501c807070001c0c6850202c500540e4072000821090828400008650300140c98844c0020f9191100044001050080c0d910041d04100d003025240c459030b207422a8144103070941c005450b09401200c01040b81d5080d160300030500340024000d008958a00b8480da48416008241381d0f034036142d807d000c1c1000015502c41880025640345544143d003007000026120900303c0c6a51050800c40000700300407404104500700340c461000c84a074031a50f44025000d940076000c00c0c1e40c20028822180310400401c001c0c2d441c020141885040d078808141e101e0704d0031a40100c4140c004624203600b8004241214485c80d4180100c618045082003590304000f91a8803414401502d44140c42c030000060100031b00c09607e8402e51030040e2643c0c1c00403448040026459600130348411402d0038000114000282c04a44c4c0c500034911607 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 849757787 1250 849756537 849756599
    0x705041809061d0705190317030402011817070807060f0c110402120403020606090403050f03091c020f0c0612040807170f04051c02010f0509010c05010c030c09 70
    0x1212009010811040e209162240c0036642c040c8881c40c03d6a0050041c1c40c0980802801c140c14080b02d1401080100e03207207582c9280c10008182c0100e045c5205600e405041940d0740c031140012114440030b112a100e0700018104000340700d540ca07542900100c1c4000044e00c0b82c45540c2e503003064a407502c900c110780114048103114070001b440386c1600992035202e4400c00c3e00280080c008282241c0000c041c0102d43c0045006210602d0f8041240710381c000011620588285816076009015020301480d0708803a01011000c6482501d0a002c01d01203000840c81101015510341c000940e2044503114240c06030081c903075030142604280d4119a801e001d9901a80e10640712561401340c140c0c880e0f8801d546040740a5014511400c0c00c0000704498020582207649484c02d01c0704102d401144646909580e0242184000060341c00180d0002c3e90115410440c0c0c0312541080161034162402c2c000a129510301540c40d12501c1e0035070b100303041c8000716a076206180c030b4442c01c0d50803400401c400040d541d0b4a03c091 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 849759037 1250 849757787 849757829
    0x110d0207020612040501020301050123040b0a0e3003041202010e01050712090e07050309060403031805030318060108120d0903030b131d1203010306090c2c070504 71
    0x4040c041d1000d041c45180001e0f40c1e1100300009000d40d01140c1c0c81c0d4001004110944c1c1c0320040e0401181072441711040400c4003026100e0501c80c1c0c1c82089580c403404a034488050b4091400c91b01900f00140040040c2c1d10501c0c407601c1d9400002c200c0854242d4802507050401c24000709890690301c0316050324550500c00d4005403074901c0481012810408100200c00000fa075045508801080340e85444180b641412199544440002c04d4442001001d00400807c2000042c007280c0264140c18005259108104c10038001c20341000c014100b8030001043c041d4080d80741080a10040762802920096606e86000f0741c0c40b0206040c0e0a01c1010f0207100e5084020181d40c0400c0b1128441e00300018418003a0000caa502c20828450258035981c031400c03000005048001d50034480c1c3d0100185c0040625003085e5001404180005004681d0310b00c0c0e00300c00c00055190440213884484400100d5803000e02030981c901403001d03c3e10b42042403450214034458003920641d0141d40e42c0e0300015a00c240c6102c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 849760287 1250 849759037 849759041
    0xe040b06120f060c0d06030c060201090309091a120c1e190302090a020c1509010c08090c21010b06190306080613080a03330b030c04060f03020c03030f060310110d 71
    0x449120445e69a890001000401d881101e0000b4000c3e0b40021804480c581006050a002640701c545040d05248285490280007400c0c0350b5440c6046554414895242c1c0c03d03107190406408516401c24102e020000c0014440030200340c040504031006001c0c01c0b0f42c2c98a07a070359012148030094020482c5804225560103d4020f450042c41d00400c5442c3c809403410035001d61407050762807031820f954918585034695417002085030300c003854000405000c5540d0010545031051003905a540700108491520020004e4111801c42c0400030403240e12002050b0101010072091400c00c8042880c016000445500214480f03106100c28501c1201c1c1c0103142c1c94860b000d5210320980310415544080c0f0440c1d80441122880c0c04000d4055182c20b12414102c0c214018511600a181070507014410006400781c55000c0f02c003076400e54544640301c080c1401d415006030155990105140c0004020460340ca090740402510419048085030b0040340000d036018119107413071a289062020400c0281100d01a603 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 849761537 1250 849760287 849760297
    0x30a0234060e030c120c030c0706050318010e0705010c0501020f0406030b031605030d080403020c18071803150b03120712030506040504050a11060403050708070e18071e0e040b06120f060c 82
    0x30b8095908e07100e01d100310541010855007008000c603801005119a007a09044003800060300f8a0007040000140c06e41280d60300070921030181008180c8030344c10700704031081d0182c500741c3c0404002d0548a0b6203403c4040e016126100e0b02d41d010744201c210492400c004c45140d0000c445014020b800c60070810241110f0b104030081043c0c040d40310300203403150580c482c132040d860119110741d1000d0b000d0800c0e020042400a16520310200000205018404a0055007041800488000001410000d04408242005021340100741646c001150500a020800111360382040702c0b55401c100076a5a001040210b800a8602034111303407001090400044810f1031f01d155558000b40405e0800d0790303036525945412815040b124040c1c1000400b00510f21407a600030f034001130007080c2d450303500481032240c554038411882041d50702c080d980c40c6110445070151240025042c40d465160b09031629040030710040c40143c945500034800030410741d90a41022400e0440780491001800040c0c030b41040c800e00035004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 849762787 1250 849761537 849761557
    0x7080606030a0b030a0f05010507030603050331080c090c032503020d0c03020c061501080f070306090c030c0f1d0906120f0a0b06040203010b030a0234060e030c12 71
    0x3c1c0302d181c1c0f9141c1e0b40410005028512810004540007010315085003500d03405031200742454100745040c4001000403080d58000c813501907410b40351020906602c01811000988401d02c1e120904010032203140120f40c0101e100016150481241c81c0d444e0602e81520044424142c2e59082103201e0b102c0c01c29111031440c3d034007018500903007001d0552890742e0446a803040c000000c0703603001541000f1014240881036001c99000458249032000000180c50f01d10000d10103507841c42c84800081155000b64884070240040e10420070041d4100e1070068000c0c80f50403450340200d40509100d401e07103841024201c0d81304008002920304c1e8a0395030b003030060300140500405d5000654011a24003c442000032054044401d030050200c2031440c107018145450140c00180150300400040c421030101e07030201d1b600101c54040050365034203d1b000120501d42c0d03584c01924404003a0b070141801c2d0300f00720412070b24640640d00800c01c0e00341d480400c80d52445084000700940e08541d07500012202828080c00a20340 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 849764037 1250 849762787 849762791
    0xf030f0a0302130902031f09020a0c02090a0917040608100807050d1a100f0b030906070804030c0b0408090406080309030d0e010c060c080f1303020c09060a1a041401050307080606030a 80
    0x240381d04d14041a03030021103141243e20501400100d1584a400d030030401049244011440c2c055030801c000c0c211000d4920103030140c1a001d003c41d1580545612000c02c031703074100d150140301141841d00c01040da4064030950b0300107921140400c004080f018a441c0032030790a600103000c4140703040c0c14130031442615101501c54003803001c0403140308100fa5004c0703481038049050341c0d045c19003881100c100000c030740e400c801041b00081c810003405601c0059000e0700408207081c29191a078803490b00300c4820300080c0c0c009110080385824401008040b4001d468031590440e01441238980705c410340f83e903070b000d0160320542c19800000070041c0e883c007811000c010b07024180341a1030101c41507280d0300c003600c0c14841c2403000148100c3c02c22200380300810700709070440c0f11032001c1c501448054030000d5031440b11503117542c8103158520104d0240d54031024050004c100030000e01032104200d82804085820520458100c5802d00c1035180305503103e042120300c110a03039120020320761501000e010258000030320640d1055 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 849765287 1250 849764037 849764039
    0x30609070e0c0c1603032604060504020d020301090b10140105070809060405030f0606041d0a02040b01121505030f0106030b180a06020c0a031404180213030614090f030f0a030213 78
    0x10340074005030010300840d400c40d541840c40d510b4010f121f00c510f60104000ca1180c02c14040c904181010304a4100d60441302c040f44039110fa0000a416040564001754190f1814960004210b10300c0a464421501c441c504c81507190b559004281001030402c0d1680021020008040000e0001c40940751200700070307101608168a5a011038640102e200c05030606520900c1004440d1074117000380c1810310541d19143c4007203002030801c540c7d04d10200074024030968450545a0f11a4428280c030b41c0d01c13000070070041c0018100b80b01a19440c045600445011317001f000d00700c0e11002d0050281d45c04032580b00d03401c6142a0b0b01c4441d024003c00025000d540c0500661616502040b140e001a0595a1501019080c1c001c458540588488004259502c0140003030001b042000c5400c49118121842444003507506d450341410303520030303081503000181100e03e094280d0050300e020207034044c452000c010444540c030306c0c04913030180e907802000d20048941008200070020a48250094101c203e00303103024010701 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 849766537 1250 849765287 849765307
    0xf1518220c090e031804090501201201050d0201020c12030d0930080601030c030f0e0a0b0a05060a0312230904060e0c031503030d0905011a030609070e0c 67
    0x321040c10815614004201c1c03080c058080d00d03206801c25000b44000940c074101507545542401c24180c0640fa21580c2e40d418071100b4001c080d0003940d1741e244940480003081600e088012600c1c1c105500710200c030408080003290b241421115100710940580007003040d074040a003009000c020380ca03024030a40c00140100011000d20f8001c880f65248540c0030180045d5082d0500c0c901c074002c05044507130301941140600b5030645c00c00242900b2880038a00400e000e5041d54040e000780880d0700802d40000d1400f040c86000890214806800c584214122141600d404140800740c0720181c56095100c180c0b00c0c0208000346903080e028101c210035080103c40c01c039110254002d6a0022078601480007800960500189032038842c40014061901c1d007002a4100440850040d000c000d01c0030815031400c9090040c00d5030b0420503585082c09042c01409603000ca8034002e401f0300b114002255101c241c004032981e143c80c0c08241148544a80c000410260b072610516400d090005400e120b040281042481c0e80 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 849767787 1250 849766537 849766591
    0xb0c070605041101030c020303040f06110f0f0306040b01141921050601080604090c15020f100f0501050411030a05071806020717032b110a080f1518 65
    0x4960f01541c484100030304200009025151800209401c54101b0010440040c540741d5506003459040340d070008541d200303a000240c59105000f1981200c01c40450300c40559047d02c001144266000d07075040c020540007000649094203201000003604209215400306020500c0d5441c2090945160801c540b0044034000403410219504103000e043e211801c005455800c0390342c4d150001c038180d404021401140c0c8400e41050058041c1c040989d800d2400900024030801048a06c8032414007a2580d041810755100014640000c03100342e964245400020310b4900b80c426112031081d1b0701181c51660380d0b007100c144002d100c01003c441c1402a12005e04aa01d00c5442c52710000d04480d80081c07807500d007056618080800c1700000e40c1c4075540104a80383ea94039160078810f801d00c41100802c07080182200340100502541e0031710101076400807401c0350b02583e00c5a01d0307500407550b83c11140881d8850b0101510005007400890b038100d41d80c40c9d060b840564400da031441d88901030f400c80c1b40d000100c10400740300e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 849769037 1250 849767787 849767791
    0x30109060603020301260703060f0906060e0919081b07060906030c0503010b09040908030c0d0e0102070c05060c0f1002070210020d02060601050711030604060c1b02101d130c180f030b0c070605 84
    0x2b19590b514100d9100300a2548110706c042c0c032985201a0307031440c0c501d403070a0351600ca0040c650a02d00c0c11440142c2000004c2c415070f5403000402c0c0740ac601081c01c258407141c0d24544c900c10000010381050340056014040d10035042082a0b540e90716245070b00b8030007019500d0b031155201310b0b0000c2da00c1000e0030120b144800510b000b1b109050206540c2d1000d0109402038905250140c1c2e07550b44100702400000c5c400d03400d0761003107a5080d1001c1303032039002c0070a0440c1071208403015001940a01c0142d00c00074020756005110303041c800ca45a49006c0060320003203a40b40c0e204880000560702c8100030a0296010300007a1507018401c294840c804030450000c0317801c1c05000d0390100d4000c0d40b6412058181d0b6082001a95180882040b10364001025000145030042050051b002c3c49000003038036402c1030440110002c6080040c00d54011300034526480360040087d01010070000e0303144080328003074080921a50040b140e6480c0e411004071f0458035070b1a0386410250050b0802e00741000400b002a00b03c0c01058 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 849770287 1250 849769037 849769061
    0x60c12010e2a030a060605030c03040b0c070c0e0103140318060c010e12091c0b060411072109080c0f101809060f05040e060a0f061a03010906060302030126070306 71
    0xb54503410444211010f842c1c85411880030311105208010300700140c10142c13603100d504540300c049941c07280300300d0207498032810102614030a0750b454040303000c2d002c07d0200c5040781c1c8a40b13610303d82a080680110748900492140d51076403000ca03051000c0d81d203403000c054200000000e00000d84540c50000284c60040c25002401c150b48003c00d11205d80d1801c0d0b0400070400071041c801c1001000c1d180e94010810100401140c4155a030b056180d503100421010380e51890381c802540702c91149016070340103409106083c6e001c0022041d10300402c050b08085080380072040060044441d06102d0010000254400103100342001503000003e442041908440701c01404101000a500ca09050b1a511840c0702604520b00490401841748040000026000d40c08201c200c4000307a0030780080d20080c09400694010664400e0a9155040407000c210095040320f4209508006065076910b080d402e0340024840d10004440c03040595900b0320819500d10000900001038504268a9556050854051180c4c607 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 849771537 1250 849770287 849770371
    0x110c01061d01050102010e0303041b030b04081b010b0f012717070906050105070206130b0409020c1005070504060f05040b0a05040311150906180d05010c02060c12010e 73
    0x419000ca40c5000c1d641c003400083c4000c2c0003040c22044d082c2d41e00d220203000100128554124505281030010000f005107611100c201302c00d0920307007801100c0b60010a140c11403004010600c03c00d460051289004091000e802d417805050395100543d2802d40a800464000307a2024156201c1c00703412800710f0151000c1100d03080f00454443c01c8510300011034000004851800758140156a000b000784c6100170f80c11100c1690307590541900500e11580e40c1e0220503030802c0401e000c52a0030090300540010203c0c94226516402d480a00b54292441540c4800c042a410003040c401c040c03141c1c8001201c84c07a0340c1403552070141d6600c0c0022031940010050400194041018810044021000001503604864512081081c0128520b1500c541e1043d04d1080d0b41c005100c9680855074106c220101100030414100d0140e170b0b0600714041c01050688100500400300000d542d24000c509440524500e0701c40040d041c0e0030203e20009808015190040020300036425903c2ca5118080c0f142c900303940c2d440d0b8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 849772787 1250 849771537 849771569
    0x14011409030a030f1b050718021308030a030f021201120515150a091401170f0105040b0f2401050a090e0a06080c010c021e04090c032603041203110c0106 67
    0x140078080d03d02c46917102040e80c40000c0d01090780001c29a080d549a98803179000c2d03440030000300000388694000740064201c0d00c0c400050a4a020015042d6440c007618280320012014414201324420300c0712401074200c0c0e020040c0480c40c40300344407107001d61240080300e03500759965140a041030821515280011004056480d640c200009107034000c1510b07030000d01c000b403c07454412082c4da60500501440d411044000d405441c0200855103c2c100714a000300072906260802e45581001128405078140b100004180c248a07440101d00310704030703032950000707039982e80c840112081e510000f0310b842005000100450950115445a800380ca070300c1c43d0000c0c80501e03081826040041e403442c0c59041c130203aa0079480240e280e400d08012210a441c00020b424015500010300408500c1340150608555000c040200b100c0340d94821202901e94081045160401c000c0c080c5034402142e0040681040107021400c2502039017141c881c040c00ca00b521070420703410000b040d0842c3d0155000ba0410b07030220031 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 849774037 1250 849772787 849772817
    0x60e0901060510170f060a15030e0c010e0904060f06030c060c03020d0f0504290415141806030a0902032a09040206071202030c07120303140114011409030a03 69
    0x3040f1400d4645810807503c240900200304010713580042c2050b000301c10903c000786091b5600d4002c40007610919104c0b08a51060101c010000c054140c1401441c0c82a407451140a40c0291850365864000906852060b03440c0d5607098054107006051004403515010040001221403035604060081503403050b10156480c24001d181c004d00c814400e091024400c94210916400001c5a081d5001c070781040706800040030b943d1184003020507a03028840000302d004030340b400219074411016101130343c8040013401c0b080050902c51164031486c006600d0582c062502c1801c0410241d40d2240903c40c0020759003100b0f4011031b00b82541e80b403440580780708101c000d100d0301d5041e500005c80c0d04816100c9000d01d190580c0030854074460320f2000340040c401c080b5403843d0302d442001150b5031810b500043d6400c9554032440142f4000450400310003003818a00740c020000064107195040700c0400c0711450000c0303c2d9000550f185000d01c054442018010443d134119510100035030700400e03220355102000d41d03540c00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 849775287 1250 849774037 849774049
    0x408031f030b0a020a0908011401060f090e04060c0c0c03060b10030501140d0203071805040b1302030a14010f02071a06030a0b01030605061c030210150f09050a060e09010605 76
    0x210840c50300c921140814808030780720003406640b1404070703a401039481c65040c10585086081d90f11555466081400580c44d90101100c1d5504840054451a221003042e40303003a1154001400b8281c036500300c1c1c200003400b20760355402c1444035540ca0b09110788514041c1d2074140d121440c5410544916032160124000c0303085c0920354003104002c501d010441941003030701000e44a80a101c44a10807480c9074105010755800307218540003040b1085005800708146140c0c1006800c00b02c2c0c1c203a031403820520003e0700d4a02d690f1803000d09141d00501600301c6208541c0e8240e0400546151401217650380c1041410382c114030710042917168021707c013100c00c0342d900c14002200c46031b00505c00e0340260032150029001542d24407003141580d61100d4045010f13954000856a0383c44200e04030045510080c50050030305401282e02011002e808109005d16181600b00310311400b054072490085500d00c40040008000c0f0f94001c5070040d224440100c1d41c59600c40454118540c2900c1c22a800d075550300003004140781a03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 849776537 1250 849775287 849775321
    0x313030302071707030b09010e1b090a1116060e011d010605010203130902030402041407030b091f0e1f0308040602060106030516080406241703040807060f020f06040803 74
    0x1082d00c080380100c10300701e03680721a4140300c010406d10f01c0c02d01113100c00e202074000480d15048542200e100d2070044200c1a2803607180b442c12801841100c0100f8910000d0340280141e02c4000f544003464070082d103050902480314030000b40c0d9825680d80b41054000300030b01440c94000071040098260105c1b9400c100c2c2190031a60040d4103541c81009000c1600341c0c6884484100d0ba0340360001078503646d4600106024042000050b40c054a08a08100070a60944d02c056006d0324180c800c9102c0d41c1d10000500b03500040c46c01da810030340302010030410020001400903640300301030760305019000100c509140740c0580079420480c1e244001140522409a04010260041107185000d20980c00d00d002040c1d031001003c0505410401e6190004046c00300e40e070060700c3c0c00010901c241c1410800901510340c00c0342c07103010b2400f01080440b8410400d4400100761400d0f2503441c0081d24001e0714040341654404588000042980200040d00c0c0300d544080c481c0303e2086002e0300c82a40d90340f9100708101200b0b03502e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 849777787 1250 849776537 849776549
    0x613150209101103040e01061713111002010e070e1b030415020a05120406020406230301060819140a0e0f06070e13020c01020d0b0d050d1b05031303030207 68
    0x81844422001e03030300c8001402c00072946080c2a80c18108800f003450861045070031403081403585400009130aa888450090b40d00541c085d0000c050302c0b80b5000d46810781a041c0d010740a04c8544004101c645001035059010758183c1c000058402440d8440d07a0404803540c0c40804240f940808200d801d070300b00c622501440ea804104a0328614107651501d08600406010040596011500b04c41481c02002146c401d00c1030003031000010b19003881c200e800f81d8018001c020006031003035040c0701d200d0440040c00301e18008568415007940c0c2040b01c203c0d00c6000042a004421422032540c5140c030700240301c3c0c400c0054200c03400c0000c070b20f842014001924140544164241d0041060071008800420100d401c07040c02c4c50000c140140c01c900203039a2900484410350783c0c0c1d1001a00c071010083c158001e00380f45a1140d0140500190041000b42d44030302804090442c3e0407010b00e544000344500c2001c0c9034241c032008508101c1084e40c0b541e92071a000b940e0b0301078109102000c03e2040c907804114040050030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 849779037 1250 849777787 849777791
    0x3280801050901030b0c0f09040e010e070902360d0309141c060e1e0c091008060703050405161e0b1903020f0409020309072c1501090305061315 63
    0x455541c0c0c101051100500c4006c12100104078403114400c010100d0312107850040007400704800308000c482c000c1001040003240d03845010000105181c250090b118040b001201050b800c43c1207030300600700076140c44500f40d0070b034001c0540c500040d40c1743c8103480302c01d501954414891a082070480f1401040c00f441c2c00340b003100f4400c042e141038400c0440390343c0b51951094011a0206050480da482c140102401c0c1900756241c01588107140d40000300340110302001ca81940298542c034198507410340c610700501d0361541040300002d0400340243c000c160000c0c4100203c3e81603036031001a210203601380d07070030584248c540400610142445640b07000003030811194524031342044600005090300e00e603c3d1703803800e064000c5502002146040c0070358006002460f01503540345803101034a0740300c001c0f41c06480a02441461f520644060790608020f0b03600d00c10303601c214280c40d803047c0d4401010200250b5810071544c0c83c00400098010710019000c1c8140c1801c814901d002e0749051020b0003085440d00000c14 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 849780287 1250 849779037 849779039
    0x7050a1d0c0715020c07080607030903090b0f09090921040e15033a0306080609160905150d0606051c050a0b040f21120e12090303280801050901 63
    0x484000e50001d01c401d500d43c00503079038100300400c50b00f010a0b0f548401403601641080001c469010740180c0306062207a554501e0054032103040c0d810500a82c20f21020019003800500307200d00f8076010281c0c11021080c100c1750320910000f070216002505c150781000c03401c404101008900c41c50142c0d40d41020075001c80107803508510000c40e540c0d07480703014220752550b117605840c22501c0c40b000302c403258070300401d125181c8843d0303100d0040c0c0542031a1281c80c00c9071040c0d0001620b22040443d10421459003d070307071030342d102d40340580c2040a05000b5200702c0240500651211544e80c60f001c00d84101ca11941000c50814a000d003004900c100341c080d6a49011708400c443c000094000c1024054036501480c40061516682884820b141041d01d00511907441143e0581d1700c00c4100840d011b8818160b40c6d81101d08000c00880015943c40381100c1b40d0a6000b2407280c801b03050b25901a0a003004064100c90030309088a10f550760b0050724050440550151a1100c0c540581c4004a14003400c415218440d0780c0d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 849781537 1250 849780287 849780293
    0x80313031505071e050906130e10121b0504090318060c0b5b0602061605160602030105130504021503072c01080a050105060a030e07050a1d0c07 63
    0x100c40e0401e644c0d04184400380c2401c1215000d0000d075203c0010140015848040240c1c031071700c8030100c1d03000350000100f02d0000125140d03802000d01080e00c0c05da0083c0c0c40e00400e80d90361110b540600d080500d541c14000000401d494030380744030b10085c05000e03a448036003c034251007685001c840d141d00010200a00a0034800210318803050684d003100440f525071031140c41601100780310510140e00c600000c91604500c8040c55105d1000c6000300c807840204901c00c0620080002030042c85118003400341e0003c200042c00c4180d1094040048101c500303040c1d140c9004079885110024140c2030841d21983e000c00180b1017410000d01400016806040401c014145900090450f0001c091000b1030702c40000002a046032084212081050541d0480f0300401008607121542850a0710300ca03000951840c0029040c14250044604840000c0c1185280110301202200640090410021581300d0407200140d241c0784d0345400801001140200e00b00d00c00c034500300890200d0050034048400c401403241c1408 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 849782787 1250 849781537 849781547
    0x1c0c02060709050105090a1d090d020307031e12060801140a180b0c0d020a05190801030c141207080d020f0606030d030f0f0c030c0207170604061508031303150507 71
    0xe443e82402d1a03500c030804d050019040558641003100c11700030302c2c209050f00441072104240291201c0c015104600100c0d0000c030b0b41d0b4018000c0c00350010380c4c1000031040d0542d103030f140007822102500e0100c0080c90f10007508010b40f44168007070340087e99200f07409840c0c0d54501c1c203a250405d103a03c0701800030002001e03034400a1040030038054040c04640300441c584844800444004152031074041d0346410b194140a81a604024082c1c030201040c206e1102405204800e540c0c16a680711880c075240c10f00f002413910700d9070840d10b0100d400480640d68132400c1c05080241c080144440b0005000e01905c99500038208032031841d0f919055449201440441d95003c80c1510903c0c1da00d14000851201544003034000c3c002400090742000c1c9810b80c0388900c0c80c4c0c903401494440700b02360200c5452582d1603058240c129480d14090701d15800040100b0001151500051900b058035030308801e52a85405030706007940d028840a1600c1d000d520340030420008108444490800c074003c04010724900203402a01c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 849784037 1250 849782787 849782789
    0xf0e010504032a090f021309051315020d1b1b0c2309150a050607080904090503120c0a081509070e2704050c0906100507030e061c0c02060709 62
    0x443c451840502a20040140c2c0b8040042000d01424004804550025002588441c4d44054a84c80260b004120399035140201c40c041c058502241039941d80036110740c600280300921040405d602000462110805401070302d0580c2c4d5002d4072100d03a0380e0404000740510f100380c1070b035010081102407110086002036110000720f0b500380f81006410000030101101285008011551010090302441a03100011009200184081e03400c0d2000603103510420030a40030b10130380101881410402cbc0d0b111810f298215003081d0348150102c904094264180083d400000c4032200643c0d038000c900c00e200b1076803103000a90803890403404101c40400280100e00d4080006028401344440c603004240f00b0349400b0100701d80c5001904603244080c021860a843c1c110f000e440070f5070548a0301e80854541d00d002c144143c0120002021200d07142c011550503503598021141c15001d01210f40c0458025807103000c0205208500c040c0040241c0c00c080302001e0031101c401e810901154400020003600a800c458600 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 849785287 1250 849784037 849784073
    0xc0907020136080406080709080721080c01020703081905070818070b0c010c201914070905040501050a0e210f040308040503100b0604090203091c0f0e01050403 70
    0x444441442c41210041c40c1000000900e11000043d001610b640c0c00038456000b28001d03521803100302da5840403d0356482060044815000c0d8807411116001070101c01100d0f43d5210340c0180f03003010203103407845007260030455040d00490206010020850500d4500c010b40720740c2208104880d040c11900140720803c024a80d07502c0b241c0000d804a409501007000900502080f85060340e9480d4110006004e000d111a00300003140110100903600c1c1964800b840c000b00c21130340104030030b8030004101645005201410b0f60b84241e210ba001c10350540501456001d842c0c00507012030070781404c1c13401d103003114001040108894549001c7d00071040002c80c1c0141a079041940d0050f01c2d4518071f601003401d210f1782102040c4a40d00290020401c64208094812500100e040d00c3c080000258a802034a00039200c4a0b8017281c1088184079812056010f10740005a1404807808420002038007501c404206003020041003190b6860050903a000422000034034007031a102d400d06240d80d0701e6140c4007404060742 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 849786537 1250 849785287 849785351
    0x20f1912110313061d01050c0c04110c06010e01030c05030c0f0f062712031303083105041127010219141b010e04050406020d06080c09070201 62
    0x66600c000040080d9541d41840850401d01e0960310400603024407064003000559030340405c850032442d070042081da500030007100c0c0034250b40c100d04801c200051103003040144080308107000c1d0700300030070041145502a01050300100c02550541c1416043e280c0290302140c441d9024a0f0307596040d44441c0071801c2000815100a618403042ca00080c15a002d00043c2429000001000085040a001c07990040a10641e0703800d9103c0c200d51074050312841104424600c09181107c10000580084028600303d220b01020012400000400d4000c41c0c1c00000c0320303600c403480028140302900c4d240c4608002404020609031408010800b20004851140780d8484031400407a1101c059034024404c038a560414134080c00b03a11803140c50940d1741c0c0340c40011011028450041403c82000b907100c008416510145c448450a40080d410030020381001072003220074640a009241030003006000e2100a404602c0240000c1100700c018070002440081c408002c40e8180662000b544500c424071002c403072100140 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 849787787 1250 849786537 849786557
    0x1141509041e1503060506030303012115060b1e031306090f0803090f010b0306010e0402120708100902040b0a0308030402090408070209040317070908070b0a090503030406020f1912 79
    0x32020702c15401ca0900d9020b5800d1460385150303e52151990f5058038030034401041942c44160a040d80e0740405d01541c4816685200031a00329501c1e104103400440c0b01d1040c08501c20554a020010713603900d640031007140070300800d0b4186441c0001c140c14584a09c01150141107190400a041171990f080b14003030a00380e5a8001c40040c080802034003424182c000e985203549082035030510703540d11400503603014154608542c2841c0f614010074203d04031a5041d100710500e490715001c2141d1062000401d6555100782400011005414014030307004d410508400505400280148015902e003100c4151144910301d40500003e0008000d03a508580c068a5a10441c0c0d107502e440c1d4003510400c00007a50240380601000300301540403041c515104400031000b046601c0300b40d41952004100d0040341d00b103030801c0100740304041888016151184162402c021103644e6080031030700b158400d03000000146c0044134140740024081107100c50000442941d41050240c503194280c0224080c02400100440040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 849789037 1250 849787787 849787811
    0x5210d110c01020a080406180b07050c09090307020630010b03010f14130c1b0b06040606110a06050a09021207060801060f09050f040902040e010912020a0b01050d081608030114150904 80
    0x2300300006002d04140c8281d07030741d4003400c5c00f50743e13072426100c424415000072000882e81d440110a5414156014002c0342c00e00c4403025000a201d85151128540060841d8199014040e4036510740e00030408041c41031798950505d403802080095981204040005101c103050081c0ca030200300d02000c902e4224005500b03080c036101150411091132403c0290b0340c8801f825018881250440340c01003200316003c00015568181c19070302c4080c141c403000c10980044901c034000c10b0300b940055034003040882001400194542c0010301c80410035074696900d0303001c10014401140c111440074050304150800c881d040c42c4c6a03000512210440c002e0780d021f140c0c04101582e180d1115004420a1540140b003800032001d0020705a008154170202075450f90511202c0c512518004124100600d0300f20301c05e12031607030804040c1f000034010706504a40001c0b04010100740c61180407080c1d08510300c92200155a5454a07400100d040f0042c00194803a030175000101d600717000b00504644040100792000305010110030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 849790287 1250 849789037 849789077
    0x40c0206011403011d070807050121050a02040f03061d010e0a080c010f021803161d04050f030a0906020c030309010819151403061f05210d110c01020a080406 69
    0x180105030141c1c005c40c00c41c030452408034a0100340c44590048582c030039510030044804c0103424045122a0071140710b40d40b000c10450300450340c0284010809842d260340c4090088162980d1b0b881603403213594560281640d41da010700045100e104020033807000e4083c0c3d450342902d644006400410300d0400080018001c8421f410000013030304615001c5448840d40100b404801910440340c900c24000c1c0010140c00d21040103119044d0703003541841205050a040b40c2107124080035100fa00e4900c00c008600b550000100000d1141e42d5003550783d1040c161070314034041d103003401c0401c46620a400034042d072181e90343d000300c2c940d50000303182e00710158002d04200000010600c0841f09041c25100300307004101400c5034441802401c4e81501200c0103961140a0b449001c0c5020b0898201c02800f2803040045203003848040c081044803004062008980c6454180740002c1444050049002c100c041c180704042449a01720070a02800a4454020b040d078400c607152040340540000c0c4000407680c266450024 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 849791537 1250 849790287 849790301
    0x7030b0f0306071e17040f060f05010f050415030215090a08030c060c07021210020a090905010b0d09032a030305010509070f23120f011215180203010c0f0806040c020601140301 77
    0x80003c251740c0c102414074594010548601341da0840c2045500400c1078600d00c02c10b41203a800c0b0803000c582c542844100b0015045144444099100766040030025035914202007481001c580f048507901c0d10404280820030b101948090280e8005028103000b10300046030780c903400740d4120041d5070340b4030041c400a40717003c03200384010310948a400301a400300c800b00d03401407400f019240c4810345d6860351100300500303858090040f401944003d10010900700707926049590813038864145030101d28031341b1042d1580d44401c0340b21070085040d00e514210916816200c3c1902500c015254a00289000ca101500c1001c04100010402902c000014000404c00c201070b084074421620f050b0340e030301c5414013543c4140f10503940d411381800400c000250004172006071094181d441540020185401010799004243c0490710400700185455940c1c010b0b0360138402d4908110032070b10fa09111409080c2c005051010040c00503025a24003a0481141303500054141e044804042d110b050503292403010078050004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 849792787 1250 849791537 849791567
    0x30804270c11061f0504020d060b0d09120f0503060906040e0a060504021f020706030509330c04120b060607060203180f06160c02150307030b0f0306071e 67
    0x81c0c891501250340d88405182420b18101007101c2e0291a101522004007404482d0030203410341440e0104554103168010741506040b1800c0001c03803594482c0300017669030185201c024240d958032250302c20000d050441c00c0001a56141c48000c0311042c260180007480081e02c014410090040028001d545682000b07078403c90180c1620402c00342480c1410107440e081d5400c0344910507500740000549282c400103462460182c6c001c1481604c0c1c02021703802000c0c003901042c014041c4000b010b81d08854519501c1d005107403415590a50703490282000691440585101c68980040108100d6031010300c03100046070307800069410243c2c5860001801c240304001000340300d140040200200041c07207015a0300440742c40c00036542d81da01642c1e07859884032421641c14012031600c00c803520b4110f2081204144251028140f040b401d4854451000c0d181c0040b0781c1040060b44680007212141008113803220001010f070000c00c2181000c01010700104c5480c80103014040005440b092142d00c0b500f041800456 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 849794037 1250 849792787 849792791
    0x140403030c0609240b040506010c1209120c08010506090705040b0a02011812110309010c0b07111c09080c0a1203050708070c0306050c090a06050306130e010e0c06030103080427 77
    0x101c8850071300d500160107504d9290651515800307221500b0240100f078413500f0169541c01d01030020380d42e10070080d40f201032275108028001d0800300d28940d8240c1c046680da40143d07458400c41c3c0c90f11011a00351b03900102124084c40d0b242c0c05205117075802c0015101030701c401c29602a140d44158104038010440070f11089861041c240c40740c001c0c00b034021030340c40207841c4555900d0540c40c00000300903580d01ca511350aa000403003080080700810340c6103038822b03001075207840c190100c040c6500515103000c8010b4682d0003007810903260f86000c3c070740203142e54000342049009408a1118600020035a0242d44100c40c6801c1c0d403841403404142c440d208403008103a01c0704041d80c860b2203a0811070f02c03086080c0002c0b80e240346000c0209800388070420507103001120084c05400031909107070b400c589a40000d04095000442c607402c080f0400028020301400000e0380b80002820510031001c0391910015422040c0218010801440851014421030b41039441c09a00e00384001e0040b804640b0340d01d528100004003034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 849795287 1250 849794037 849794063
    0x40f1b1d0a0b0901020708060c3a060602010606020a02061b0c0a0e010501030c080f18030c250f08071e0504020307020d1103090315090a020415090507140403030c0609 73
    0x2c52034001d090f5040c000c0e403c480e44162508281c82c0e03100c606036202a804041030000441c02800304403448070850341c84402d40b14280c048a1010035030f41442104503207094440320140152942481128020900ca10041c411041a40c022503058401c0c0511a078118000a82406400d0020803031140700f910b01924421589a4500c1c455194800c28054035001908203d00f840d0101e1046c3e00090084144006100480d11402c40d440100c240b01c40246e1502d01081c08181e0042109014800c0d01104d111948148000021400c1d1820010b030f4200c199003d00c95030062001c2c0c60005001001d036000740008011041520700c500061b51710359840340354031500000070403c415602241d11044090700352600b08082c2d4004503100d880e40a40c1042a40546c401003404504c03410046540303400410000982c0c000e03007216004031f8250707207c06a0341184030741c1810080200304001d22807541d010507545005440b0340160f0304581e52a2040d0f22010301005500640c1206001060b4403418565502c441c09101032 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 849796537 1250 849795287 849795299
    0xb060a1208030703110301180915050112063210050d060c030f0c14090105120108010c0210180b0612010c18050103020306090402040e0307050609010b040f1b1d0a 71
    0xa0b610032500900003e0070301000483c0762880c00103890580b000c0c42400c145031081061000e004040c891015109440d1110342032041426500c5520301030f20141c90322009501c150304280b801d5980244030740710351100742d4004000d04601e041083c0c0244100070502e140c651035420005401c09041e0700f08561200d031002000080041560200c15281500e88091002c03500c0c00c00e40d10212018614842c02040842061207c0356040704010f00c12100c05041c074a040c02001148120000030076086002a69911400c0070f02081d01008814000981c1c96000c1c8504030f451340c98004038492500e001040142e001d00450b80c0b079a1240454414803c41e10000c2000c0100310f04018801080b03696020450a4840e10104d142e5120b4002c69204d00000340c06030102e900c4607801c0c000100002114049507010920028002403410302001d4014212a000880c10000b200e080200315004142c01c4000b16290120000b9201d45903c888aa080b03000d0a0100e0540f26040c030384200002880785241d442a41c0c00d03404a10 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 849797787 1250 849796537 849796553
    0x50a05060f01050712050901090b07050708012d02090d14062508060603060604051f091517041130030306130b04020d0908030a0e010209010c0b060a12 66
    0x304160807100000c15403241001900e03544602c04000c0c210303011402034461802c0c0520001c1c49000810300d80f454041c0d030307240480c000c02d4001800c107c65540000e10100b21524003401b84003040c448000e4147e400352042c181d0482941101031b0300268090700402c2c150042c3c2c3c0c0301c0c403400d0000303900800d403054090021002d16407502d000303c84120341c01c0d980502c07039450511300407122130f41780115449001068883c0d101f084400d4000800c000e50004040001042039103990410300103190010358061502c0d00e15407000f070001950707508040406080c0781052810ac547c040060708024040000f08505034540c2d082070594500c2c0d1500c1260131440d40325a000c054000500c04550340c2400a516107003c0091604480d1a17200039203200340d100e4200107225460a41591090694a000420061810a0b822585d4042d211000d605485c450004420006c0369245405281c90103103080000314070b4030100c1c0c00040c0c0070100550014107910380080000e0a1500c0e096103000c00303013501d8010702c4030410302c510340303a00c07 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 849799037 1250 849797787 849797791
    0x11d04061e0f0e24190905030a020d0309080304020d02132903010603020109060503190c0c03020f0a0305030a0b03070b0d0c0f090b0708071505010602010e0d1713020d06050a05 77
    0x100c2d2500d000b80d1040011404290a20f1001000d001c401410302110104014240e01601c0181300182c0c0c1251010003100714403851001c1031141e005551100c0031144080c0c00d04207802c0401082c5820a4401030000f4006402c4a602aa0488070480001058008210b088055080d00303a045450a40e0021002d22115a54030110b0182c0004042204502c0e05041c03c2e10128400280410301e110414044a4005e80195900c11920105036821007540a090800c1d25003009040e0301140e0030307000d4102130650501c848000d1502810040001d107000f40d40080c258800100800d42055507001c0c1e51400f96800c1c000c02004001c00c40445480d03030154803405000780003156518000c501e1101c98001814003c2030a0800c49081e15101030801da080e0b16643c0003a44801c2c402c440c3c00c452020203030f011048600c5814041c107130320743c00041c3c06040c42402d1850301c40300c41c0c08841440800e19206000340c4505410343d038410f458405888c1c2d041034510204201a42104c00206000d080200304501c00501d940454 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 849800287 1250 849799037 849799061
    0x90109020415182f0d060e0411040903092102090c03180a03020d0537141215010c0807031809060608070c110a0305071d011d04061e 58
    0x7420a059481c045085520350050740b1164102032680320b002c0c0500c04d56004102c0c9407145501d142c1001411810201c40140d00103400c45d101e00c40900090180e004006401c0c104183c80801039000241c502411400103445103843d010301c51b015820b0030f0340d1002d09004941742d015006e0046424400030058050f08203c500c0341d090051241100111040015080c801903055005000750540010f0200d51550040260102031411301c01c64100d002442d941c0000800e4100320310700040304012000a260503550380034000901810322040000003d0320f81c106401003010b95628880c1c0440e40010384110043c407502618146c2c0100e14170050607001680bd400101302e8540d0100350303e448513118001c50b90103000d8800061420400624510302821410204078004e42015900d49081030004511117020f8004994503084444200110040d0011689408001e840340caa250f43c140a03480b60790340d6001d00000442850030f40410240021940050310a1791170481c80082c92110001c40400f420b84042e0304 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 849801537 1250 849800287 849800309
    0xf0114011a04060903120e120105060108060604050307050f0301060f061e0318320a030e0906030309010507080d1d0d0807050f0f041706040201020d0206011d090109020415 75
    0x6040381ca02046034290340316511203094003405c507121017074a003800721124014803042d06052101d44d0343c0d10034102000c0a40304c001180c0c9203481e0000520340c443c0139000a00038841848240542d90b4081780c102c09680040d00c001d03100d901c2c250b0004c0c0c090180c0f90311510801c0c0140380c1c0450b00a0340181c9180502c000d85078411641e03031104400f00d0449810304c140b2458000400020700009109541040c03c0010407040c12819055012005c0070130402c800f03031800f00d07a000c00f51480405410601151419504581350030b10381c0307420f40103c0d8480c410340c46c20f82e04205000518000300400c1d40191401000901800c1003140000c03101401440e00c26080b03500e0903c580105180c1c200c4c0b050068034411b04165488074242a03550451000365000b1980f401c215110520000ca50021120840010840c469009011a0420340000780c104132030000000c00710742000e401807107411011010100304040d0002d4580c0d241d40d421403000d0040c02020f87c000d61080c10807810314070030b070603c0160600741e030726a00310 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 849802787 1250 849801537 849801569
    0x30f0c150a06030c151d0103090c1e0905060d02101209050a0320070504020a170a051006090b120403030e0604050a11030f0a2612040b0106030b011b02030f011401 71
    0x845866800140100005114020509034101d50711b001030070040040c1000309103079100369200d44030303140d03a604180001501d0f0001c040f00e01591448140040468074020002070900130007154a40072400c201a002e401c036100303461a01c0b40f041000c4104030f4042c0d081003040203502d103044c035110030103c1342c00e40000d8905038a01c48848604480d0b041000214002001c01c58a00390920010b500400150024807074207090103d850400d6618451183c001d0307541c0005c240c0703444030300a00c402485d0740000c1d0030449143e405220741c010403021689400c071510710780007095540746011400340801c60032040317640c05404240300030880d00040c40c110f140d1150b000390444d4104203040c50b03968801010140781c00d40c400c2903800040b0300d4880c1501100031404030341d00340b030104c2001c400e4a158043c03000300c4200c0c07011104002c00c0c401c1c00204640074144e00d142c10300c0300304000d8000070802c070985640c6011710400010100c0071503a08100e80752440301200021b0001e6072540001c0f0302c20300000d101e03020062400010f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 849804037 1250 849802787 849802799
    0x121318020c010c09050117270601031505010f06050d090c060203130503120d09110a0f06031401050604211b030b060d020a2918010f080405030f0c150a06030c 69
    0x80c1502959411f0f9940301916a08081c0070441c0c110107455003000d1640b90b00b0f503505608005009003905101e000082c042075242d1b1800d18515114050302644042c507240040c82401c1d03a083c031040c11a00d047c0703403042d1581c800c0700042000f040070b0710000b41148048000005c6058010014080300440420301e8285942d4070300525840300800350a1922090f803c000b11507040d5450360112040b240a4041e400e445003c170000b0555041302030f00030140304080c880e0100009545402a81d5030910b6130001c440255240c000400d00301d0059018160f00365072003900f8880000c030b0491900f1440b0b40c1241002c51810400c025005580d003450000b0b4070982d11403c00101d5608001c81c0341080503a0203803014034200d207011040c1c1040110005c0e840c01088184446d4180c004881020b4006d4081d0703d01c03040c4a144038000094990320a1000403018021003400b000041107021043e28182a98a41e1481d690030026a61a00b04040060030f0101a0740c1c060038454610380d40e42c05041680c0c480d450910449031108 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 849805287 1250 849804037 849804047
    0x9140a05060f010e100507020405071106100b04030f050307061d010b09012105070f0603020a0e0118091802090405010507110a0503190c0b040b19020705121318020c010c 74
    0x50302c1e40d000ca0b00c41e0703011a24a09080e050110800070910b8454140803d55000a0030f81350300741c55a0000070350541d409802c80209021241c0c0140c800714964030180d01c0d107c0c0f001000c3c01107200190072004014170b02e90500c801031048408065100c48100801240114109100d0b00c0c0d451044c9410742c0303041d0740314415080203680386060792290b20780e001d800f04600926044451341d02070100d8040c041d0700c00000c4c450440454200207000240c401680362104c0c650300030103500c06184610b0400c20240d012200c508007066640042e035030204004a01041c00b014002c01d10284810700a400180c01c00400080c0b00c03040d80003e0144909541300702c003c41200c00e03d075513208080f05002d0682c0c0c10400220000c1c00748588800880c0c1101c0c06c1002d5402455141d0780c00020044030b0a40e05154a03600b00301d6148801144082501c040503821820107115850f03040c0d554205001d4045003600000d101c5100a910003c0d0748014400c007d08140c21000890200e0042e420519901e0915800d010440341414011 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 849806537 1250 849805287 849805309
    0x40c02030706180b0414010f0603030e01110102130b0c07080706090b03060418080309070b0a020304091d0d0906090603090213090611131e0e060d030909140a0506 71
    0x15402942031600c02c2c1c8440d0020007402c0800b44409403002d55a400113042c03007428921490288880801801c1c612040030b081d0b5002c0c01b42c088001d483e0400c1030002075001070110720307590000c0c82c24201981c030a007451030084c421401c1e01916101041c60014030304002000500c15101c60400f039480c4280d4803080541da0306214020a00401e815031001d0010790b01800141d03a0112001b007000c6203001005036403e144645001050b50050b0000003040b017801010410f400040140340f038000d10f0184c4000009481c2c1c010b60050040329516160402c5004219452000d00141d4a005844241c988808080d00c0d1040c01d101c0d400104610410008a81d80030b4880d024a031600501202603122400000e0310003800d4104082b510a40d03241d680f0b41d80d4040e600007401c0d03030310b03d0305240380c0c0d141e4144603040c000501070428040074414070781c40510440c02c0d14071506401c003800341c2d5020300b0892149425a224401d80c0c002c00950340c0717408c000902c445480f070420390142c6081d1000f08042d44911081c89044114 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 849807787 1250 849806537 849806561
    0x204050112170a391505090d02100e0c0310230403050d020a0c0c0f0501020f01090f020d0201020f2b020a0f031202070209040803060f1206061324080c04 67
    0xc00c1c006107a600e03000345001040400e429803880ca20070010b88034102c55420190b4181e400c90980c200c4071070b4101891090981241001c0d00402e0082c40300b2358000d41d03c02ca600340d4102e01d107031190b28810014004020410101034003c041e0b0390701d84008100702c002000807654200c0c0d107909130b58102000c0e62001e43c0c1c01d40a9030305690341c103181c0b545502c2140e0180d0711240d070504c200440c8454544c040760000d00f06401414902aa10142c1440c00c030009140506504243c0d81c00d914010002000418102444a065906a44078460180c0c5400146c1c03c04803241249009130040500d81741a0f81500b2a107088600c07808464041c05081d400412a41d60b04c03038580083c81d61404034441e40110b40101400540c54022580c058600b40d0b0310350100d0b59140c1b0a64044520050100a01807540b41c101d81103841c0710016140c1480e03032031600501598a00b405050f03580910b8802010a02d02001500490318044d00c10011501c0203500e074960340000e040f03502c62404203009105000d001841c09e07008981707905031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 849809037 1250 849807787 849807797
    0x91303020322050306150901150e040b010306050603090304080106141315080a0c0801051b0319090b04120905010323090304050d0f110904021804020d0204050112170a 73
    0x140e080101d0000040d005511140b00650001c0001d255504000b01441a07103010050082040b070b02d402e101200700c06811040408078004803585502e0303400001d280a100085a010501c00b0740c480040c0c0040c0415000560050400000c000c140d52001005200716044e4130020000d056446805c10b0350080f404500d0381c0d0106c0840c440280100490b00a88412220715404402e42c50307a40403090701e01a03010300100c4a40d900c20030100700c400d00070b10a96600c080325410004100c00c940f4100342441c40000d029035000078210300160f90f94441a07000c01d04c1c45500c03100701c20b45800d0a04220350764014407042d100001d100c0490216440d4403074003c0b9107905e1425011203c0809104046801d007003001000c2ca210341c4424080040d42d6510280707540407090180000706240b00c0f481c20421010702d070781003140303026a100c0b006102c0140c907035921242444034042d000d603440740c49038400641d02d48000d4902039030103800c0400124044092108441940e4800c1107903100c0e200a4036010003150080242c0710001c92 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 849810287 1250 849809037 849809047
    0xe060a06120b0102011d0703032a020d0309090216050d030e1018060207030e031b0a0e041a040302061602070f050d0813090b0103140603060106050c01060504060b090913030203 77
    0x74040d040540380ca50140000301d40c4015164401281115241d071088450340105010424960060400d005034140034000c800301f808235510501d0401c504a170028010821100e00005042c82942824060410000d0943d5608040110000d034000c000c13070251130600500d059086224040d208058210b0240000303803020f01c10f044402d00c010603007079402c014a00c03d140300304400500244018080b00b840783c2c80e0203035460341590905180040d0b410005d180072040141c4142240d659003054421134460b0fa40c84145651030f8501106107074511100c020a0443d10820300c030406401261441c421981001c01005c51101d195003242c1c2c5820394425400c04440c5031070140421304100c88044480c601800d059407401c1804440160000e115503c21403205c0d0303881c902103c9540c0d06009441e46c80c500055941c20508145000946520042c810750703040c1301000400c0201000290482d20051100500c02c002503560b0300f05401503075000103a180e114128040c001940c10001d80002014160140c0c000c50800b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 849811537 1250 849810287 849810317
    0xd08040b090a081611030a030504032d05010f0513210507080a0207081005010311041a100203030a1d0d05070507030c080f0f0106050d021e09100e060a06 67
    0xa20291205546008002d0100e002c03410500080c49a0344001c941400380c04c0150820118000001c18036521940010401d100401c2d800015a0260380d048201d01d510403441164124490502d03400503070314031541a1414080c40419800039841e01c4c0003010500c12507445001c451f84607003031440c0051515810049215071145c043c82c0760443c030380f031505006140c59840d0700d078058250404c5500e540164442103050102010511a001c3c160096550070b101650465541c1b050014942d013006000701d503910440190400e030515640355501c03029144448610186100030b45940c4129105044603007081ea1116402c88011a10103004802038081c124051503030008031215800004156418845d402001c0003003502c5001000c02030030848018074940700501d812a090200d0b1054101c00c507450001c042103161030b070110203203002d0380c100c40e144170124888100701c80d5040e0000311203800c1011038040080800c1c4403c03080c07003998215004042950b4500d01040840c1c0124014100000c2100040e101130b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 849812787 1250 849811537 849811553
    0x7050705060c1e2d0709021206010c0f060614010809030705030a1209020310050a0b0f1c0305041a0304020109080601050a0e04020301140405011506090b0307230705010911030d0804 79
    0x10780060070640340c45401340307134503804140c0c803000902200784250704074850a18000c014090051010303e4040d0304000c040c180003074011800811641c1801190101078081151a43d402d5890690001080001d99100c203801c0d031011031200c0038036006c6001708000c2140b40d00000141c919407a03010006500d02055001308954038011102503c0c010361700c41c54002c0040c1d800b84004980e040c040c2800156518005e84000241d40d260354085024041d83da00003402034903a0f44480c110030f641c2c444003100240d150300d02241c0c54860b9601c541040c6101800029168402c40001c500940c000d995444840b03403a145801d894010a11403580d008000d96420801100a022255030040c0014000259468240001e81840c1c0c4100c2c0c086416035943c2c5004440307502c20b0440d41d00138108078940a42c840341443c10f0244144000f81014083c42103950390903500c008018804042c140004141503150802494458060000d80404641c40d2740e015204001c075080025042c4994800ea5071908101d0b140c584403005 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 849814037 1250 849812787 849812833
    0x9030a0528020a17071802091513060e1201021201050a060809030307030903110d230403080f030c130605030604051819030e18090f120d05060d12020307050705060c 72
    0x18082c003172183c0005d503c403103408091500ba50040c10150340c80380c1490401046600841026941c2001800303030907c2ca5072110113020a540aa0810192050003000003d00e108400d2801030503560000964180903001c81c00f00c1030407141d0648151072074a403980016140356508982d60201340c1c0c4203100040b5201e21a8001c2000f823070003800c003940601c0501a556040120b000d828002013801000f10b80300002c848800510b03a10382e030f0b100440c10705041d0b9941002900c00c044402c800d00d8000710204a0620740d20382140c0701c082c82d0900407101d055551001803c950003c9812a110341e150000007150704d4000d0000b01c0c0020b800901602c40091080400c64483c04c1c0b03484150300f007100c01808038a0302c2d1101e403200e40002d114482c07002c006140c03101075149400000010140160000e0a00803800c410801c2600d0380100d202c100890180e80d080301080d07410f828060040e0000c50700340d684400c1d5903000f0008012560207a000c3c2d5031002c0d1500284240c901c070b480041200c0340c2c0581d460080c45007070300700980 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 849815287 1250 849814037 849814079
    0x1020d1b020a08061b0c030403150f0203100905062e0327170703020703140a0221100603030905010518060c0c18071e0509030a0528020a 60
    0x1104050355000300707040420303503003080501303500400500c0702c01c01c0141c909600c0d0180200780325140221540344030782c80c1d00403440000d0510302c0b21405e00030030078a42e40140c41000d10441c0b04545038030349292030b1040c4400501c905030b0002c0c5460301280d09406c081c44101c00f03400504c00c0031610050014010346002028071103030001c1581c1e079030100804003e00b880f440741e1001e070403030300741040c120ba070410303c0e200048408401c038500320030051000000d4001c10044112604194000544a0054142400d1142081000754000000c078107140d12240c1020024004c00204412110000700e102c8030203089a203540006400318034210403c121a603c00c20041164450018464003450300e4400450743c1c542052079031840a0700050784a030b149082000c5100054030034420341d04401d050450010b40700c004040300112599240f80701407017000d4011411280009405001c840000105042407030b240c1e0a5070f02112621088804880c041d0459840301090390354005040d004a1840d000648406101d045200 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 849816537 1250 849815287 849815327
    0x614150d1211010c0f1701081c17040b0103210e0f030106091109101d01031a031009120f0203250503030403050403030e040504050c01120b1201020910020c01020d 71
    0x30b1584010a004072140201c90340c5404019101182c1d0142c12060091440b8800d42c04810040103080340024030158440082200504400c098a40880e220000c481c0c0e10074040c0d18074810f200410200744050360403240180c1d8000500140e540190401d403500c130000c8e00000b80f8030b407007980b801e241c03c0c00c007140f595000800014510344d4421619056501690550140c000003107179502031810400200d0100d401146445000415000d9401046811034141c503410141c1d11810b135052030340030200038101420010220b42c0d000030a41109005041000303011101c0d101c1c01c501189219000f09800e0784034140b5500954200340c49514407108490f0243c20700d56010304408800004034000b132008501850196444c031356102c0c21810090700c0d20742d080400b540224901000c10021483c0819240503842c0c0900e880065840c08480c42006000c181001c039903c0481070100c2c40102d6015801014152002d96210213490003102c01030340c403846410680382c05a0440860610414410f11000c0710018507007007a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 849817787 1250 849816537 849816557
    0x602072c0709091812030507090b1c0518010b0111120d061d07020d020c1008070e03010609020405040b090601230403080d1d0a020a140a050d0614150d12 67
    0x203003c06a0f900300c0b22080440d01e107140148180311142188526084d01d9041c03e00ca0740c00d110070001e00446451003845480c140101d4041c481050302c40085103080f8a90ba0b00380103030700300401c0565000c00101120180ca40c6410b103c030f035407940200e241104540241f000b515050340c1458480c031f039550150300400085961907074003081200e40c648541608158403070300305616181138400070b0710708040c04040c0c909540c0036603170007900e0342daa40500c0b40380041a80307044900c54441500c02d40b0303450401c0c5603165140d401d00d040030400400541c040c1084a4086034107001d0900b2260520901010580c0e03102c1c0000c0c519036810750701c03011000342074064401100070103181550341d8030354141326040510044601511004a015103404203000c3d420116900ca0103068804240d90000e40d85080e644280200b07542c22282d07000c1c8550700c216010f00146030103040b00c079918505280038070060242d83c88201e00c0598000125400e01c0e480030702d4086a810141403269212403540b00c0107040f00d103c0341c94000b00a14503072 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 849819037 1250 849817787 849817799
    0x516060501060c0b0f0c0a050a1e080712180f02180a0204030b07020d12050a06082d0a050a020d020d0812070207301110090602072c0709 60
    0x89114020940340d41c0f0400400c420740fa04104510010b8602004946a1781c1444802c16001003241c00740c50b814140903903a840d110300103a03000110050a41000e0070301204000c40160002e89541c406c00c29940d070444941031000e41c07282102c0c0800038040480c1d4100351410009416610305a035042d00007850400f448403c0540d041990104464080c540e6802081c200100040022090740100c55030014140141192900034599091260303c04521503c64001c0340510030194000f50103000312809981c3d0102d84118410031400f0b40310780001c0d01403140c04807e040300130086807040c3d072035030f10201501c49181d1070740800a03090041c280c260381c80050b0a1000d000078001c04010100051512081d501514142d10084e041030400d034014a440061081c2c4050610011041a41c071a0035a80000c0f00b40852030034580241035a041e44150020380b20700341c090301d441d00010384400b221615800c40c3c000d503880720009c0ca04180f101481103030110401010340070580e28995456448000fa113003407c0b00d40e580798 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 849820143 1106 849819037 849819041
    0x90b1c0203210c010f091a01031203050a060b30070e09090c041112010f05011e0c05100c1d0a0611010e1024080c01051606 54
    0x41d90b4200c00c0301920341110030607000300b04940f01209035a0061001d4030301a60100505d500040148100110840c1660351080c10884001c02079035069016180103401c04000740c0d100d20010901d11004005070011640707240c4d40c2c04466060f180003505062103030002865900c01242005000341d0000344426089a003916070051556071286a5401d01403405d000c142d106050040488031004044c01500000484038070b90703210750343e035801228045a101d20030700e40031030180350312151080d002040d074407144600c1d03082104007030900b9940e003802d00f00302003007509001d40d46070566808c542c5c0c044800d103070f400c5042021290a8441a00203009104603114100804c07001110042000300217401c401090340702c85045804c1403580540c00d001800406070141d210690080c1c1086150040142c00c00071290580090a11590780d200110f901d0307800440c11410301251700c0031140014102d8 = true := by decide +kernel

theorem cover : BRFrame.Cov 849640287 849820143 := by
  have h0 := BRFrame.cov_init 849640287
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849640287 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 849640287 ≤ n) (h2 : n < 849820143) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
