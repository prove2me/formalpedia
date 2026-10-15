-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4190
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:49:26.86322+00:00
-- url     : https://prove2.me/submissions/b612686d-8f98-45ec-9c04-25b10b20c3bf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 753417266 ≤ n < 753597122 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 753418516 1250 753417266 753417289
    0xa3b010f0f06050604030f02011103040e180c040b031906020c0d32040506031e10060207050105070203071e0f06051e090f240d1d0d05041e05 62
    0x8500e40301c9480c0a1805514000c81004003800d40b41d051419155032100841c0c00b10040000381001008030042d4203107002001070710040c040c83d01650855040024903036004c3c0345aa402000e55002d01e8444401c40d10f000e00c125241000d001e8054480e0031310b0203040300e0b509404207074100c82d640d600384804c50a8441c108540107015469494101e003016a0841c800c0d021100d00d00345c00001a20303400c00d90700b002898015101211025114a526615102050f400500380d0f1102e20154803441c0042240362415903d0000440c0c0564085c1c4064035100d000440e107d1040400194255100c0b00c020442581d95901e0f02041214201c8041d045680303c03048040d41c00804d070301200000b000400c4078044008107082083c072106108080c1450302c0c6004010440094001082c02e102c1d80f054004401003480e0b83c80b1038042142d280c85016902c0f070b01502c40d0710080047e0080383e643c5802c55000d070803c2090010703207200102103d4607040d0415150141c504280b014031002c001191506013000039154882e40f18820 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 753419766 1250 753418516 753418541
    0x1103010608060c1e04150f090b072003150f0403090e0a020c1501210c091e0612080324040e0d080702211315080405060a3b01 55
    0x7980e83c0305074141413036000c84200d035a08070440e08020401202c030201d0005a464500c90a0a48010841d41c0042c0e840e260750380e1000e401140000b8140040040006440740c84c00310b000c80818055645c80103150f91403441c00a102c2d40f41500c81c001c00e0405102c1c005c010742c018440d18040c02c915484254032030a40800380c4000c060150085001c4140443c00d2002c00303070b54481002e00c50421b40c908065161515448203c2c40e04040b540c42003901841803882106003c2c2100075014445090150000001c0407150b4248074020340c6000c10110310007032042c202162080e001018641583c0300d2100001803160100c2a09241c103445420031036003500c035401a48850201d51018104003404024081d281000c000c02c0841190004010219000074040400600b80c0325020360b00e0310352417140707056540c1029540180491035803014000d9041a4000c47c101d105a10403c20748049403a101c0402003920642d1100f03004410b0301c058944043d00f04200318440b90241c1d0103103040705d08190408036084481c0b004020 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 753421016 1250 753419766 753419791
    0xf03040e0f01051009030b090c06041706010902040e27010c030e01140403200c0a240c12080603011508062a19020a050d020106050405160903110301060806 68
    0x4000d07049600c0c1c8460050200355018024030458032001801048103000c002d01c00305d11440403070300b805010450100d83c2c1e4000ba000c1903030b685c0c64125512000382447e446101d42c9c85540b0011400780000e000391012610b0801d0312100c02d4460b80911044895148216a030382c00f14405400140718090245448076030300d9440c00103940c409030030300c1401d40c1c00813441c3e03401c000500e0b000d20000941c046448008250606040045011789224131400c0022902c41e2903803102c06184042000346c600c1d60301191841301e1800074612288120380a56820520801c0500411401c0040011281c011354850b540b0034402800010303001c81452084d0041c52040d00701c105554000010054100390b40c0c83c00420102104a15030b80c540010761110403140301d00400344240482c124442c40304a4001c100c0c0100380380e40107050b100150b030500f40c000d00a0030381e41300c0e00d88a80c1c100f002040d0103101403505200d000c0895510786030720b076085407113101042400840240d0103660703403e0000b44120091044902400042c085d4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 753422266 1250 753421016 753421021
    0xe0f03030705030a112107031103180114091002032205070f0504020c03160201051b060a05131e03050c030d0e0d030510060c080d06080c041a01021b030f03040e 70
    0x1401101c0511382c5000d8001c05c200442c2448080081c00c01c030748800c3d0104c00610503540c142084015040b814003039401d03400c02005014203a18100c1001100b0f8420034003c1042003c1400c8041001206840499243c0c01a040064042c0d10a07001903912280c00102e40808400340000404601c2c0385e42d1054880707400c590818002030348001041c41c02002d00711820350925030003405103900c0e0700c40c078500c0b4035012100c49124421039015005840e40403100c3c0c0281c110480c5034080c0d00391501400c0318490320707491400000800403030041500d0600990400744260311302c13940480c0900b00e080400002d90900400740860081c22600700001d0208031403d510100710032144a220350700d041c2040d500c3c0c03000c0c035050100b0000003d4004042e0f0b02152964501001903070114280000b4070305c1030103103650b8503030305250005c40c0f02c2c013000603280d007001d2060750108010705c0d0f24070044100070721a41c00c0e035006130407074012202c1c0440b1142c20310801c010b000702030310780c0c240f51803070360518581c00381d0320001d88025007508 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 753423516 1250 753422266 753422281
    0x1e11010b0913060f06050609060706060503010e0601060318080a05030703110a02031215030a230714031e0c060d2901110a0201050a050c0f3c0d030e0f0303070503 71
    0x14013a5920b00401c0902c0a1400e110010b4402c0c0106505503014000c089210300c188850343e0007400082502400810005001e00490398641c8405d0082c0700c003090038103401c1002402c4ca03210fa03411480e00000c025003428542d280888480c1e0003e040302c002c15407521900c0c3c01d4907a6910060000301c0441c0c004507640c0c4404102d0340c0408000624030959144128560710858030042807140c2482d40c0011501e20002c40b030701118050300c54403d045032103480342c0f86011500b1a8480069000314208034100c903040881a000b4002d10903070035001c9003054000c089404028100440a00004e40d00f1100105002c184d180c00c0070446a21401070b0720032080e0003800754000d0b5800c1007400c0841414580540a49059500003030028455041c0c038004004000910402c0d4880c18000c00114040640980d001030110706034240180512082001145c610440c880010281d4400040d4001240c80007411100000c203000ba00103101000071441e90340501c64220005504c140001c620443c0142c54880d03e9051014 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 753424766 1250 753423516 753423521
    0x140109060f050102060112060c2105040606230909070306020c031207050a17180a03030905010f060f0308030907150309030f09061205100801020a02010e0d1e11010b091306 75
    0x90245044d034110301c005000c0c07440718014600286800100124075041f030303100111028800c401000b10140c80400703403101400080c0d00601d00950080c1c5003808030503100d01c51840510841c002c045080703a480f1600012904000d045281e010715008183d448560783ea0312184241d0b03000c07000411160b00009070742c030400600300524607042807131458002c1c02d040031b1540103820000c241c0c050007140342406000400b10300a940301c0da022000040c0c1900d92440941ca000350250606420482e0f055082101103401c100c1c90344900401c903504901807076045807554a034168680d2014284c490709001c0c0c4040482d0b0b010780150b40801540c9290741c0051518040d08006110401c1d21114108005034001e080040c80e07032040e00161144410717200001c190301c48400413040041d85a0000103103500120300d01c61181c0e010340c010541c0d009100103644203541c0104049540b01000d513958003914415605c06ea11480c454441c001145501c0340000400300c01e1100042c10400302102c9240304100011901c108100c140d0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 753426016 1250 753424766 753424769
    0x1515050301030803010603111b01090b0105010e0f0f04020c011d0f01021908130506010b0405090c094e010e060606030105040e01022106090702061e0a140109060f 71
    0x1854018115411a5200c080d24030041c807504082645502c00d00d0900f50126040b0340f409483c400b01d12800118800d40e080c043c20505006490104040f000062994060000c000b03100070b00400082910701c446042122281c41ca034030040e0480d60a008050f106d140034416802d2110020b0428002e503c904046d41d17290075881d001404040c2d0043c852010544420700c1c0000c0d002015003803c03020f60395000710516283c2c2002d840035005100302e000000e00030a094006105a4100303032601400d50350f603d10300924505c40c0c0c2401941004103280c40c1d044c0201e00c9a00301003001c09c943d01c131003095000110400c041a04000001c040010407a4a00d643c0c0c010134460b05c7c500343c1d031550241c0304500e03010001a2041c041440f5050069803640002c200550302941203130101521468203040c0e200c40756003c00c0321f8800848100b80610850400306000390f00002e40705102e050981529501e252101502000d91400500720944003910380c0d199002e13141881c00b03150b01a01104000049180c9020b102105c10782c0036 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 753427266 1250 753426016 753426059
    0x1140c280c02041d060c1909050604050d0f0c03080307120e0d050309011112040c0f0e04110607081c15060905040c0e061b1c08040f031215 61
    0x3032105014256000440a0700e290b0301200c00140302c0c050348080016141c1e401d200034445000d01010840024146409004207280014200700c2c0315201003003c0c0c03208407143c0074103640100c00384810001450822122041944181e028035043d00c0d141e40c80b8852000342c0d410440c1c0380c10001c0b00300814103900c0050252900c1a50300d013800350b00c82918019850b404461030240c100b0100100048070b0740400d4021800d13250344084500d950b030105071034940d03000700151001c55421405100c0094050b0b010000042914002e0200c0d012030f840e140d5680d41100855070300c09070090000e10085c004034090802130056003020075885240c1600c2000072030b00b1101c0840b86424042e01ea20740502c91582d0000214043e110141c0d4001600143d080d4265000100d407000e10f94800c0c4000343d07002d140f04980c0541e00c02d012054007192014000c0c2854940c00081c00c3c01301c1c0c40040c04040006d40810507003015107102c03034000d040c82c6001c1c0c55030740110810303210380f41c0910032403401000003000601520203068804021 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 753428516 1250 753427266 753427327
    0x2030d031a0114160c050a05060a08010e04020d0b040803041407061211040f0f03050f01060e0a2a0504170304030b0429070f1d06091201140c 62
    0x6240707144039803009449003154100920b00f012040000d030610101c416011401c10a5220f1850320f15000740c0300f00d268000d941c0100c5098030300140d41d00707228081d079201d409552144000b913801c0c0142811152402001030380e002c116403002c00041070030324110a01441c0140c603859541d10700350a004055006080e1241450360000004004c5540d00c540c41d0344611401840c0070981302115005281180107079008010f03010b00706400040c40d107540d032151303c0843c0d00c120305440009405000f00c034200d03138961113542a444000000100444920381c005030720650b070002c406900e003544001068480380c2560303e0b0400300e0310006050121110019000e0603882e880740086150504660701c0417640b01010f4402003500b544840104001c00d244400042d1641e480e440c8600140750000c4014810050320340041702142c0004c3e003d00300d080201080710390a040c05408a450710410505000700383d01d0345038102081e95a503d01d4120000c0c41051614040c103107000070b4a480d680300035481440b5900c1e25580c0314200700c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 753429766 1250 753428516 753428531
    0x1f170f180c06090409020103020d050a1d01020721170a0e0f0a0203031602220207020f030a02030601060809010e060103061b050427021204060c020c0105090603160302040b130302030d03 81
    0x207a4000031610f9043d001d0341d0208000c502c0b031005038081d000301d102d03518000d400d0004000e10700711541d2021880c2d40d04142c0381d16480c100e02c02039500700d1261a40162103005080401c0070744d10b00c10034441142845514048026099404001141e15016540c00340541d0311018510a0400c2c200a117059401441000c0c05280e200c50b0b00095a034031070040d035002c403800d14004c18015507403185066401e42c901d0081c12854522500701c0b020007036200744012446028001103030720b61410b001801c200c031150b0180040c0000d07400d00310191a00ca600900500003507480d4424011540b005220542c02940300d6000801c2285101100315142984055031a080000502c410003454400d80f543c81c00c110b0340e51007050b00329005a40c1c0c50001c0d10580c041034418070030010520040101981c0542454801503098030789245072103004540e140310300c4000545c400e03814030100c0c0b032080c603c40101100b041c0500300180b80a90b13502100c0750b02d07001074054801c5009400020000e5007000c1c40380c148c00880600e8104240c8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 753431016 1250 753429766 753429769
    0x16020708150a020f0d1e0902280504140103060f05071b0305040e040b100f14060912060f1b07031202130306060f061d1f170f180c 57
    0x2980300c81e00c09a2490510700c0420740300c0c2c4590707045030103011400c0c218a0780c0c0c041002c0f22402a04010500408000700303030b03000542c0750000f0310400c200142d0003494401186101c2d01d40e400000700003016480151101d2100150f240e490748240030b8590032010b0285115031650500341e0441c5c51010180300c03100c0c244010410142e6101c1c10300b82071443e019100b050030801c2400d040702c09001e16002075100b1000c0d8400e001c18072082c007580a100b01220005d081c203094807000070480041c0f1900c0f9165051084510021182c42c2a501818100700d01409044200c041010301614250041e10705480300d40c904020b10115266058082845e1909030b04100c0c60500b0950b80101101801000c5a08042d4003180055800e481446a04025900102c0c1841860f84601c402d60014103c0c0c840c1d640400c000032222403800b002d13101140206640100005140400607040490100c03a49034100c00b0815840c079112140400c03034214030702500c04100b6900043c80c0c5102e100c407050b8540300403568143d1107850303c800c41c0d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 753432266 1250 753431016 753431023
    0xc01031b17040314040b0405100239100c1202060405070b07080c010e16141c0312090305030109060e090615030f0f0a02100504080604170d050403020616020708 70
    0x10008114407050303070b03960404544056100004903010400010006000300c2800085c20603100110351410001584007010303650764100d01c05013041c0d15045840000b891080c1d1401380c0c5505011031590bc01c1590321000a4511484041d1000210301d001c4446d109001510582030882841e80c0010f04040c03c00d070f00c40a9a90146210f00d20240d1000103004d01048010410380302d40c0b034682c000a20403480b010b80e2054407400400c00c68a0020544100018007000b840111121240f000d048044003181d1040718008807440b15409409020580070340084040080c0b0840046030f000383e80b0241c4075410b013604441a031b4226400801c00640c82c80500c00d81c003402044450700081c155034a280350124600109060625252013030495008032004408424004250400528802c03240c10301d140003061016501c0d030059014500b00382d07000130009400030b4005507000c0340c9800c42e602c10900704401002048107440c41120103c0c0160045018449090311003001070381c40002c02c1c0040c000349410f00c14020303607 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 753433516 1250 753432266 753432287
    0x30906090b072c0d111c12051602060705010b03060a06030204140f160e06040b190203070f0b04030903080d0c0206070503150904140105100f060f140306040b0901080c01031b 76
    0x402e5143e8113010080090211a8645040018044201c50800c00c058541640688002500d400005030000c4031102d220b0021112042910f01c15181041415002d01115400c40345080b03a9940d42c46400360155a400c1268a01c103410808022981c14114414441519646c00c14922585400010701041d9084036080d15440851450046484071a5070030484144000c08041c5800c04000036022034000d00440040a002c01c9011107007403803122131781c4100c0e46c9105502d0040e1030a44001180000201500c0c59590401d0291810007250303922500c51405543c84002d550301c885035165440c40d80c40f601400420f5000d480c1c0d042043c110702e04400b40700342c0e1806019486100384c11841c0020108a0a484458501c0c90000001c001907d00510740c00c00070400c5020700b00b5106030b83d0000040c0b2600c500850344400000d42d82d103a4440c40781c0a80c650b0280c1024000c0c5601076114000001c1c15128500414020100c46004000341e1082c0000582141d000e5800c181c480b001c3c5030a03641e0500e411a000b140d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 753434766 1250 753433516 753433519
    0xd0c0311030c04020406030b090907150f45050f0d171b060c030702210c0a03020c1e03030703081b04150f0c030806090601030906090b072c 61
    0x200d0841980c00064101003007104a40d911501c08207020441c154564421903002106440240346030f203a050000b0703500d4885110380a800400103142c1c0031003c0c414460400440c6072800c090690102d200403451240305944516103086205070038500c0280240704862104044103494650380c9800d00b0041120724500840c120b002da81003891000810401150032441c80e110150300c6034231035024141d8960814000903103030285104030000314045c00c62040484e80280c20300e800a14008200200f0907001820756519076461035814003200812400500c550714569110364094204014408200b010401c139001c0e04281c100c41c001249120780d20001704651440e074041c00d002c0800c0e5111041d1310544514072010b10096800410005103266100b10548005480c0b61a0304800320103d11080f2410203107240d020b00024090b801203411424605040ca4108006150105503030116454800039a441b4200454014442c48200600903a11580303500a80c1103010003840100c100c054101e00680e243d21296 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 753436016 1250 753434766 753434783
    0x60e040318150c17031314070e0a091a07020c100905091620070504050417070b0402010e0907020a030305090c0d030e0901120c031104270b070f14070507090e07140d0c03 74
    0x50b11f0303041000100a12038400b40011501c0d115880f17001610849108580344200c4c024506040703090183c1c201d11074000c2c0d81c01894681000000c01080800c1c4034424420710028210129140d16965815817250003983c81040e1800000100203201c1b402c0340803081072000502000321070004000c6071031011a0400c950201d2192180e003000c040300402040800480d8030005000c0b8104203c62102ea03105038002d8a03000910b145590600040501c11150040140c000d4858000080c1c0254403003500001c5110440d80c2c0c02c0c0c40300010030a40d8a000009a020401403080c03545546891400030703002d080b40d0800070703000f104581d80300120741e5107600004048298403800080552101e50002d01c8289244568808010f002078031003c039515880d000780d840d9140840020080c0f070090381c0301c00c402e11040c4d945100c014100c00a1000c01c0d044020100c441d8000c2c100009502d5040b80030741341400d00d13600c0140c1062450003114589030742103018514000c6150402c1680819640b0700c90038226904070200 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 753437266 1250 753436016 753436043
    0x609021b1b15030a110a0207080106050102151305120c070311030a08030c03070e030304090902040b2b080904050a2c0303070806030307060f020405011101060e040318150c170313 78
    0x1003070003611304c5d91801305c510381c1d011800380c0c0d030700d54001001d40844144c20001c00020b61a08012a101c00701d02c03000c400f09d0210200841d040001408100342258003490030f03141854100c50000c40d0319400200220011b07400074000f4400d00003213510308003200400b1002020707510940e582d4003003107000003499404099008800240c01a0080052071741415006007913940ea103031100e003100d00030135007901d00703901840c41c0c82e14207805410700c28880030007a80e40810030901c02c01140c3c0242c00e1010303012030480740715409102517080e985450207028042d101148012070840c140758620701d0b03000410100224a0b02081c4076040c0d8420000c070440c0d0300210b40b40352100f4a5510500440d1641c030440f4001800b035850480745104203c401e03800360094070300983e0f40b64590448041020300f81c1d4860300900710b000084201040020b8060707803803900c1121010f80e421001710b0380c4921000c461118030702040701123502801480d0420440400201080782d42c3ca00150850034401d1400709881314154000340311a810004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 753438516 1250 753437266 753437281
    0x7050703020a05060903120901050601090b0c030f0412050105061509010806061603080f07090b0d09020a0807080105060301050c12070c080d0606050d0f05070804150609021b1b1503 79
    0x30b205465504801184c1450801405c01580d07680801c2c08030354002c0d424800300b040311a040c020ac07801120160349020285040551901c10340c1c0c800c1c03241c0301040c40204640e07a05204038101400061000e12422005040641042400c1d10b01c001c2c00741f40306445081842c450303804040c0c1070300c0899600b841d08083c0313580c07042c005c034010748079008654444c0071087c5100004c00d03510082d228440c850100c803002054540d548141c4200507140544491001c052101c0c4511030486c1d8440c00c1e032140010415517007503513540041810101160401d40c0203945600c02c0244030300b1300b40905074004001150242c907080741c0340318160110001800074410420241e405e47c1c140308451007900c090710100c80b070402107540c1e01e0741c01a00c1581300c044405007a604001c3ea07403070003d06a1059512486140d1501c10341951203503180c401c030b54014900c42c000350b5681e0348017280d41ca41c00e00c050301034412400d0703004450b00045c040b02440c280c001d40b03007824519544015a82142c584021902050070500049030300c0c0d844040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 753439766 1250 753438516 753438523
    0x9120c030a051e06061f0507300207060f050906090a0305300406050702030f01020a0f080a0203090c09071119030e09010315020702270708011409010b0a0c02180912120705070302 78
    0x90003078062403403946820034100c11f000207070704171302410910b003c410310201400b642c44810318422400401d510034140d0100038007070390040140d4038000340007516001d40d07031002070030800d00e0381c13c1504d00c1c1c0e11000745904a0908445420322050310381001070200041042062654400d5015481c01c0060116080c81191000c01503d0410180301c0d00a644940d88150000c0907103618a040500150b450400304081380d149100310703800b0f502c00d14081d04210a8079000d0042e49400940008104102c00e41c081200d000c0500c507500c0f24855a4407076507800308150800509030201400094401c001d0a4010030000b29078503c1d615070b41b0424100543c40e10424000119000b84420741c01174043c00d03000c041d0001400c82102c051013041a40c0302c002059032201c070901d0510702c3c002c410540055071100140031003c54800030b401e0058161800000b008510b902040310007909403040342e02e0310400380a008014200344480c041d410020804641031003e4640c0c034030041c0e00094040d00500c100040e1a105043c402d2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 753441016 1250 753439766 753439777
    0x3040614040b160f3c1e1a09060105041a090105040c030608030408101503050c22180c0501020a030504170f030a050705010501060f0509120c030a051e06061f05 70
    0x32500e11082e11108018504194180c1c4024420300c102512a178080e016154a0404480e08001d0319141c240e240d00b80c51041040c00700080d64002110030380c09030f1440b44d49560f58483d881d0705028200d1545850180002d4411000402000c18150391a85035640c48004245044650450300861228110201500144880d4004500c140400100850000000182400c0e82c00b031010041040721500102a60140c842e070100814640004619003410728092650b84c4001c40c0f40c0055070f0012514443c0c80c021540360f881140d50f4485401c41040520001c5c00d031600090000b0300150100700010b9600a20798407450207087d144440720f141c51a0100c2041000202d031180311f004980c0c3d01c4030006409026500120030445140d8282400803418070b2044840b00b2036017a054456906080d880000c1000e04101c0034401401480b804c1d82c0141da80d6410000e26174500d025001505c01d8600d058070920300d144843ea915115036116200348011925400c442002c43c00d03001000d0311081142840495a600c910f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 753442266 1250 753441016 753441023
    0x7050901060c3302030f060111030d050402130509150f0106020d0311070c080303040b0a0b010512090f190c090614010c08131d0a0b130e070305070803040614040b160f 73
    0x1840304003516030f0154000d50294540c4c44859200342e48000044802041c0e1108800c55508103108001540c2250f81045401601c000c118102c0d10710380c4420102111000c6401c050968440c18414510001e180241c54021603041c840340403940c1407840c081d65880301c01e00c2c0703102015130320580350a03000d427a181500c04441d071180d40101e510740d075015825502d4009032804d481140c2d00e200407840da0105c42c801c4903211103040c0c540c68241740d485140161740c41c80040c81035829001b15110559030314000e10500e560642c020039a54101c0300d040c24805145059904422515450140140066410304c810040810024030702400c0e10314151906195901401061660006220304d010400c1000c0007140d040740360505c1c0b0820300950700c0b03008460030b0f82c4607031160344c0c2c0040009140030440080d03a00204600c02c1480f04413001d81c0e54960340d40c0d2070800240d1019a8a4002040502665500c8000c003010b142d0a1141c1e41d0070541007955100700f511410815000c40d100c0d02e00c00100300040100a0142c5c140c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 753443516 1250 753442266 753442343
    0x1425081303021002030a02031602010e06070804020424090c0504050312031003120e040b010318080c070308071112070312030f140703140130240c0207050901060c 71
    0x3001e06c4460042e40003620400c4440c3c03450f6001d202418414494521400840d400404ca00c1e100e02c0070507503810320058401d03608a51101d02442c0c1000112820a8408904024840800345810005400c80b000b109074a42008001c000400045d500040c2c1c0404003035150b40d04a80e030741c503400c0082c0041e174040d0b0b0005105150424803940301c2504240441f4955005440074082c11a08100440484d9207403803042029403c541404e1300840e8540d0040c02040180c6030440f08241e84a86422005c1e4000c0301d012140c0b810401203102050034907070030040007000c40a005000c5581076540e5004d030059408801c1c800c056640c00c02c8450644d0341e400c000744c00c071120704407000b2504101d50010040c014138540d0f04a54084c00300001174500c15044080034040030342164814010740700b10002844d21201c80162144124070300c200316145000000020500c460440001e80c0010100c0e001e400d0002e03a078020b40c451000000100100c44e000f03000b08403510b03401243d660002040180c4a2602c2c101540c07600e85200303 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 753444766 1250 753443516 753443521
    0xe150f1507053019080403210b0a050a05010215070e0a0303110d080114060c0708070b1201090603121b08040807030b09030309070b07050102040306142508130302100203 74
    0x100e2032210040d207640d1004a00c000c25030000b8101100e4401e544031444013480c5641c100201c0707807056419030f070003a2181c50002804a0030710301400701802008025100e9542c3c40e40c5c000e40b103240285402d0001c0000342d6000c1c0f151450500043d4582c0381110364000d80b10540d50010351041d108076403000380a14014000c0084940703d060048c1401851114500b07036106100ca17511115025990083c1202d2080c03c541c0e100c072101c00140203441e00010100a410703c200c050101720352500344104000b60070301106d1a80c0b610f415104100741d040d0186e000803116482e0030070078004901d1101242d404c04000b400c0c0003840c0c0d51203161481c44560504005005140d000c0b901003050040414a08100c0c0d025007c040c84030f4541c5144d06071a0310064400c010b4903441844200442007641000c0d01025004500041c286680c0307032204400d0310812000e50707a00d000c10340200300502d44c161125004d040c00040c0940c40c2001c501c1130281c031050001d4100c040c0b01c100360004a041620030401c4056031403c0030020354490 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 753446016 1250 753444766 753444793
    0xa0b040f0816080901020f06041101200f010b1f141b010f0507021b0604050127120201120c080c0f040305030d020a0801060215040605180102130e150f150705 69
    0x1908800621401405400701030110507c00181840c055070f0481421013145044100548091615503040303518811141800007401c05d007401004801d101a40020034080d01c0c01c4d00b000f409529060448100072200e00c0c0d11316001e50301050040500554a020300d9070345440b415941ca0f05004000b0095140d801c10303450b0243d072078858200c2400f8a41a40881e0107100d05441c4e000004620300b500241c20820601c420040c40d84a1a113200d2030600320030075001d0b07030040c1c1c00d04003254800ca40c004d40741c0c0041012200b002c5507031104055202150000c2c00308100804070100625002019054104d03c19010400306a04030468088800541e8800100c0f5940c105016000c4041c0d080700c104400410000c03000000d4050001c1040c9502c549025844000c543e16542e40c100104000341840054848101400e20b80343c1c000d1000b04a140c1440742c0d5544000d01d070404804461030010241e5400703100c130300e42d02412034403061549241d05004a075a629161280076101c0d0440c0260075000e4002e00c1003080c3c09050 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 753447266 1250 753446016 753446033
    0x4090c05030313140f0102060f04020619051903020309030d0c020102091306080705030715180e130507091e05060607210e1c021909020c0f0106080a0b040f0816 70
    0x84420900c0075508401c0c0c49070800041707800964045000da0060b8002407441120b216100c2d03400303880107001c1405c00804076503601c0b50681c9408030700042000080e0702c0e80c0015074440c9801802d4800d19041d840c62030032518140e20f0f40200b6100d829490f854a200c940300074001c1d019500741d5000689802c294017202c140d0b1102604441c0309030030341030283c0400030800703040101e80c21040e02d00c0f042c90300800c43d0418100b00c400164444074494030b030060103000f040103c0a48a1540180017a01d48100d8025045c10820309001030795005402c02c7c1c0c030f00001d4030024441030380b60700e00c1440722000010340c0303580b404081081c1d4403481400a201e0086a081e00300d001441510311000e64600d40e03141440e41d403040041c0884100702c4500301c181c44189030068401441c01103003011221040540304400035503100c52203810703600402c000c00025007226444060a080900c102030003040a40010a651040f0b51603050101e50060005026884021050824041d1a8003210440c010024802c44007040c1030400c20308 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 753448516 1250 753447266 753447269
    0x120d0306030c0504061a18100f0813030e061308061e0106020601120605060f030607020c01030b150f0f0c0a051b0f0f010e1804061b08070e04090c05030313 68
    0xc2070b0705161008111824544940c5040c3c403c10b155009920134180884551500308456940e00c4c464448400b40b80380d00e441a5011240130191520005411443d4000d130000c0c400a1411131a101d2054407000800d50040803804903540580300c06070b0b207810300464191070076016081145a40309401c14000e2280d010220005480c003694547c000030317601c07404102c0c1c076490b0078440c089400700700d104200c001c00c0080c2c1c045600700200500c0140c0d8035140501080c02d01c81f0445c0c190025070070401e502001940c0500900081d07079400c60b501840e20a00ba003241800780500f14100c00c28002c00309014202a02650460310710711403100031200213106e5854020f6940c0d10300d5180c0f144680d903040d0418031604010103000808070000342440703880204003004480140d221b00807240d200e0304101c41c055020301d0305c104850295009071310200c0c11780c0c1034503030070b40590484010f8141000481800c004000e54031107401c500bc41c5045070081000e86460418142410709604001d0b41800700045109240c0141c941820 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 753449766 1250 753448516 753448523
    0xe040e03090415231c060e0f07061403040204090c080d020c1e0f0f0a0909050606061c0509150a02030a05010506090102030406050f162d1709120d030603 67
    0xa0504500c41c404052509205a954902850900f0210782e200c0b0301a513140703104c0140c4016064601c80440708a00700070b00900341d60256440c03a0300c8003280760910400201804030001459568606500103221500100801d0086036001c8045400c5550b030f03400040705140c00100c12021591a25481c540f20010749040c00d0241c420700200700300074100600c07640320f01110a142c1c2d801c070035620170a118140010450381c0b64484686040c5500c0e42d684c0c10201806403060000004034990075140c110b25018002e05060702c200424404444910655812000d078070700c041c0d402003510f84460007401c1c54000c0c2640c016848212100030442429103c1d400303944a03104150040c050399980300280328140c070a084143d80140c0040200713101c40c0d4010780040c00c00c0051000340602e081c9000da036003c50441801422a0040c04805903141e0000e00100150584401d02110080e600c4c6940d440e81004c00d0b640c0304480d550f1101181c0003001d86d0f500c001c2641e410320508160350900a01010040040043e80801c0303 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 753451016 1250 753449766 753449771
    0x7053003060409080f2d1b010e010f020d0b04020325090302030102030a0504060c14030703020c1006090c0206010905010e0a0f0b1306061b120e1f03021216020706030b010e040e030904 80
    0x981d00189031b040d41070260412032440d2400d41c0f0401c403030700c41801d1711550341190340d00c075000f20001030024401c60b20001e100c9100141c0381e445004281c42910008141284118014014000042c40c40c2d001019050080c1c03641c0610204410410340e181d00403940003030762551006c03040011000d985e801540c4102e00c5280c1c03c2004292007a015111804007061490004409000142803203002e0340c000c00c0c05150200403640880385680a2409035503440d04a82412503c0d000426420794040003001e0140103154428456581480c03199010804002c0c03d18202c0c40e1142c0b40c80c0707032052103035000e014048c0c40038089901c052889403080c40070309624411700000404142e01c90807101c0c41d070040b04403101d92020590070f49004040d403c0324490b10f040d06c5035903c403e10415070644580b024080442e0300a0980f400b60300d8280300c860390705100d00c000b404917410311310003450344942c903901003521400c2d2020790400085844030000129040385124401540207440c0002c68103c009000000d011102001c403002d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 753452266 1250 753451016 753451057
    0xa0911090906180c0307110a1b15020c010807030b09180607031401051207080a050607080705040303050304060504140703030e040e0c0a0e07140f07053003060409080f 73
    0x1800090f010018070001c15106040c08035076140b040b14000d503000081480c05905080c410080c0c141040303406002120386000d40c081d1448145d510001540060040d0241c020f145001c1880107512591003259003410440104000b803122406130f130014a000380064018890303031a2080029000071a0840a6826417243c2000680304502c03a004440c001e680840b01c4c1c03d020b03441c040c103101d132040449041303c00c6402124400f080c1880e0030003141203014001c00c001c0c480303410125009800f040d07015003900c1c100304003000240082504401184e402c076074000c00c001160307551070801c034000c81590500c2c1515406036243c00804e25501a070100360a031021981000900d28610036241d450011030400b640002c2808000c11141514000c0164030409030b0800d840700021210303818485a0001070b10310504400850060b080c0310007000058200b201c0c4004440c00441c072410800d4102d030340c8144141441c1e0380000042c0c25038a0b503400c009100d95004410548900c101d0500352002d8100580d00888514040328 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 753453516 1250 753452266 753452269
    0x201060f090207020f0907050702060f0c010207210206064002090301050109050402090612011b0906180311040c020c090108241308091908030316090b0a030b0a0911090906 75
    0x1030043c00b1f50300c00c0c2c41340ca1400a0542c00d119164010040e00403005009002c0050414000e0006205e01441601e40504401c6116003104030340c941c480c1580300310b501c91010440551181c0d0304103c00b244400000c455080039403801e20941c01074401c28030519070301c564030070105a400342d0090315169100b18000d111607a2942140004c80c0e400321006503001c102000070600d54240804001c0c441404040080343c01c4010540c4503020070b500f21041c600007414090104a103540c444199250101009400356480d0310399240c1c4001c06181400642c89241c1c2e856801007054020443c80c00c500901521302c1c00340c1c0da51392460540380c074a00c5c80c0d04240c10039420710102d8402c3e0764081052040c8800703e59060080da240c0c4618406400a9410f517400c10b001110000c006a440300f03c1100505100c4000c60f0f0324a0004100c486c40c4001050719400d200c0b0031802031140070005000c2d6005880d5500d40061049542000203d108840d94025541d0a107080042500062600010300e01d0601c196941d14450311403d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 753454766 1250 753453516 753453529
    0xf02030a0b0a061202101115010f03020108010b0702010c061509051e220609080409020304060e010c030b0307030209040813080c15040506070314250b16020d0f0201060f090207020f 79
    0x9034000c0d4046106d0908070b00072401092035816a0040c1c1c021515803940d12100a41c021500382c2001c00ca480240004200f1984d0104901c0e0141030101031f282e052044540c006000641c03d00c000800d590b0705c600e6030194480c00b40010000901c10100c1c01c0c03010381010007801c4400903041c090002c440720b2302400034032502c41c0c4490300c10214503042001c819009203900e60000074008800100c0d00c240e02088002081c10300c5001070341c0514010100004c44445006520342159031141800091508102c10012642d070040790420460340c0603200c04010307642d549000d11041c800c1c2d41d41002e9044e070500022030b8400001a003c000101c1c00c2e912607805500d0404490440c3c042c9215540e0b20000c07c00000d800a032141c2d00d000309022006d007202e4102803402c1840a54100411011029803100341d5042080c0051512180d0304142c1c1c00340c5004409403812402511088603904090920040c03003107250010340b00354003040c024510072030400705040d2582030540295000100a83c415051544c2c20b1640d4500031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 753456016 1250 753454766 753454799
    0x1103090708030f0403030509042324060a051c0c0216052e090b04090f110f030414100908091008011404110408060f2508130f02030a0b0a06 61
    0x51165003040e05d1645c00711403e03400484820307045a02d0b40d80e25010303280c1c03850119500c0004110021001d140054401100200f0400300b00d45000d1004942219519070f0003c50b000059030703281150342c414080050b10f00320741180b1800040f16107080024210b455000c0356042300060442e00d00724141e035682003000440e04460180440702c0b103030401b5080043d410001004401035050402c810426a10b94041d9016001a807001d261103464600300030110120b4441c00814420b2480454140502d41035210034078040244000c0010b6500c03c44602d003100700b08004000c1402442061003264210314203115541c008102c143c0c02224241c60307000c031041c0545101410780710211500400700b0040030400008d0401c0744420f0400c00c004200200e000f6030140a03c3d40310304a2010080c0349400d1140345100300f840048202018410f50f500a40e108607802000c0d95089078900d080721728042005d080548040d00c84440003903140c4986080481001400300d0094070400d0320440c1009415641c260b002a042d00d02d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 753457266 1250 753456016 753456037
    0x90504080405120a02220b010203280512070207090b01020f06040320100605030f061302012f0c0901151407030905150c10090b19020d110309070803 65
    0x910003030100d81042e08500145410720000c854207042d1980109403030b0030f035940b0b4054100d0141c4c0f00000c1c0040300fa0287c500042e80a20041d4682440c040c03140c84000e0103e0f02c000c0e5400140d8524040240c8901d0941300b81c0c43c40010070081c4c50030b0000c03010795180c440e4800c41800d41c2c20455086840d60000c00c420041201a0380034220325900c507501200c10b41400003410031114050440f903a58903908103e0180c41140804002407018140700030035140410a0304101102d03800281040294016450030640b00c84d82030070324a2402c00045a9018035005400c000035403410240d211001c2c00e07100240481010105071102c25a07640c0b102c201c0d180c002c02840c1e002c00843c2840c20a1481850704034010300701c043c080c1c80c0c40b2240548990000b40c4410b100b440c5105103c6003c071320607564800c2406000b1007966061400c001c1603070240c4d01ca0303224600080800140d00344080071015804d0550301294403c00c0000340405c84159503043e21447c3e0b404c103130385580e00341c400c040c0b001c07540300400400c64a15130b25 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 753458516 1250 753457266 753457283
    0x5090303030a0e1e060108060606040303021e100e011a0f03070311040b0901080d090f23010e04050a06080f0102041a0d060e040317060f2d1f0801090504 67
    0x201e44009201410a00c3c80e140d049225002050f03001110b5854803001d4803d40c80090550f03540740542d21842c201000e0182d42c85024100800c200194001031401116213040c1d04415040c1c40100450b82001031a0340b100c0a0603040081c0120034060640c8041120040304801d000c120301018184400140c101d20f496415a101ca882400401c00c512700704441080028400b18184c40c3c45004903141050a80c8101034960054032608419900425000b000cbc0090004441400c0c0c40d02079004881c88203090400b9a445a4612048140c0d100d6192000356260181c8203000504194050388003c00580c40380b00034070b002318442d03150b1625045c002c4804860780301e40194403810ba00c900c004807903803041c00ca2248150b03503000300060554a410340f0600c0f450298603502e0b010b044000200c5680316004056a2040e01d642c8403903030315940c038420840305062041c01d03c0313064440700701d8102e03000b440600303055648480c0b070341806440e1402206c0920003c000c66600e82c41c10b642d0313840001d41640d030b040c2e80081c20000c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 753459766 1250 753458516 753458521
    0x60221030105011416050601210309141f020303070e0114030609100e1302040c181802040801062418141c11010206060d0b01030611040302060d0e010b010509030303 72
    0x604c03c110110845000d80e5056140c440b09058460b10050000022107046d0001c400411101590407400000389640e603541c50010025650020f000309101c0c050b00100382a0580c60016546801c041c0c00c0c4070000240000c0001c164803032000e952500b08541c0301000454020708110b040d44901c03200c1e15030303c40104040d0700396240d60041006140b40240405442c0007810320020354442c0d80782415002d40003045681c404405180144010365a003041c0b5134060203d007480303075034050000903009000c40704240b00d11035064610700a060007900c0b4651002c0b8040d03080a20226013202c0d0102c8085410421154042002001c00d00a03117000114584080e19400c9a02c001c000c0380d29900300780000e5420040141d282341c05018125001002d0a890560301010703d07580081895804102d013981080c03086171f40208483c52681c031801c44410500006055585600d960f40300944408203a501031580280010348900c10581804e0051040c81d000040e250709011854141d03500401c1210b00c0408003401a510b942d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 753461016 1250 753459766 753459769
    0x40c0e011e0e040305070c090c091203020604020d05071509051806130b031002030c0c0d0206091027080a03050105060a091211040e0c120f0309100225060221030105 72
    0xc100400c04d0b4140328041046800298414a0800c00307041c04030000030354a8400f0000a00382c00407a00038084500b18140b0410100e03800048942e80300d0390444414001e080d15180a074208401c59000040101d01101641c012540000802c8140c403425544580200318250803030721704110990301541c201c200710f020044100c510380c010050503000641251500c41c0c404201c5000c0307038001ca4440340b90040200700c048020340306019511001c1e00300c2c4001c1c6070a0600880f00c58039100e103095020901d41c0c0c3e41440c80c44d14000405905400050340300b4554825820f03040861555000d0b04645000070b2400c400030401d440c00b0000e0f2800c48050365a1003c0290400f0307010180c21070600c5040e0b60248070104140440d80e01c40c003d2560b0150310401070846010003a080c0078484403c008c0301c0b4116000368060015485001040d141a10744c104c0d4403071541c0e08010800d038102202122410840804840e01c864150407458101044070865421510040050382d900c141c0082c448c840564941410401007105 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 753462266 1250 753461016 753461039
    0x30203011128090b220608071e02030f0711030d05031603090305031303110604051e03120a1e051e070f0c11040b040905070303090e010b07030507060e0303040c0e011e 73
    0x1007501e11782c070146144600040025100d2050307800500042d00c1d84040244c060740c01803032203641e200b5418480042c0b030b00100c0041c2d1a402880c1000301d400303801244000034440c400c85080310790790380507054920040000b2801444c90784100c0c0e00c060002580e8100c280520702c6407040d9500c468055485a0940c1c036a14032405024030400001c0c3c08009101e41031031920038003806041e00542c8601d00409446081100603800d040c4404070b4161580c2007031010030358410341e032005541e000c0c8400e0000203101090b0b03041c946002e81c42a020070700b0546024204070000202525080c0d20650344e08046015640714481114038480b441340cec001c0011080e580980c00500341c415440c881100040001c40c210200001040c21107070b0800041da03450b403019000f0820b0603000f0184002030001000c82142a6041c10200d40451141100080405c8000240f0300203200d07156105101a0100c8806e40351b90781854141541c01c4c244600801040e2107401b80002502d50114480c503281c4d039048800766500305e145c507440c50758 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 753463516 1250 753462266 753462277
    0x30a1404030e060f04152102040812091f05040302030601050a0521190c030c06020a05120901030f0e010e070504021903180b0c0d060b0a080f0709030203011128090b 72
    0xc4c810014000030a0500003c2c01810080200e83e64040c100d89545a104107851000603800340701900c100700074808a4004100e40b1041800c1c1d461455440d105030020a00c0301150480020303100f00003404211b11154001c1c0107004680c000c030201c031481d980310300410a0380101880347c1035102c0b800c403541400ca980b40d01c482402c0301c0c95880a640f0300c8600b21102c1042007070501401c841c41d00368081c1c103000300010110703c80050f191501c020310041c001030780d41076981d044020b560b07100d071080071806499a030302c640c0015a01b0002c2e00400e1140d1001c43c56000d029050300b08650101c1c0c056a6408256410148299845100e000300751210a40145100703400900140148043d041111040000480c18021490740200c504000469880081c0c8030743c1c40c215070550b0844441a1404c00218034500c0e0b00499498000690301c031a200d07644c84440d0140e07101d81c0d09900c020b40650801e1032105180034284050844100c840d00c500c03002108280303100340c0d480f4003800b080e800718829203401d2140c20084806802d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 753464766 1250 753463516 753463537
    0x130303110708030c0a0303051005030607050c030906040f0905130803060d0f0b2a0712111f06141c060c1101050f01031401090308010b0a180803030a1404030e06 70
    0x80c407182d29030315560704641c00721107410080d50011001c5010182c1c1845002c0d4041c40c0200d07201000381c10580040e4884030040c0000d8108000412a000c011034180201d51038054000d002560b44c0741d41d0f002240d00d402181c854040744a203400000341561040f040c1c1c004001d0b903c100d285d0f10350b58501041201503001a01c0688440700c0b2035400600080000b040c060095070070340e0344040300807400700c0d00d50710340100203048440300c04083c816500043c0540080d50743c050000e0800c0c111004810060510300007910900c180340705a1082c04102d040300036800001558081c4206900001c0817000f4024601c4901c540b03507100160b000352600111b41b00343c2c0030f44041e5005180c040c000360010440682561011740704500c0000e4203a0040080105815580820b829100c00a01c5020080d1b1009007d20605208441010600094034403101c1d01c241c00c0541c0e280006442140b02c1515840c0c042e5a0707800444403405840d103440140c800d281000c5400a125640c1503581c00b400003101d00c14072405810075131a1030b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 753466016 1250 753464766 753464773
    0x3110306150a0c06020d1506020a080304060b01030b06070b01090f090201050f07080403170a0e09070512060303091512090a05030412060207080c0307150615080c1b0601090c030213030311 82
    0x903c00160540020010403211003001b04d003240e02d2107103028444815902c100c042d5401082100009a0840156a840f075002100000d8404070400140d02400034225110b81c4044005050b130104030940791140d0503501c2d903a401301302d8140700c40f042808803900c03400080c0c0070840600890004610742002094141d20036030505080551301c0d640c01c50094003400300c961002401042e07003c450345d8045004500d032030007101c0c1400c440c00d1a40010f0200d20442a2a00030394950000141094904004a030170070714015054000e005911900004540c010140c00030b506402c59000c500794610000c2d4500d113894014004d03604e0140781c00c400e00c41082a014084805540a0025801040b4804c0140c030302482c654000d1950f859152402008810301007103020720700f618101d42031001c990040e20075903540c401401d1a1140ba103078060071000501030030000000450000c51407500d40940461224100c0d04259410721041203032410942c1a030098407042c0c59600f07540d820800100e4490241861521804001e4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 753467266 1250 753466016 753466037
    0x2011a150315030109050a03140f030606210c1e071a1b04060503092a120a050d0c0302070e0702100b01110111091e060703050a020709090506010603110306150a 70
    0xca07081d40c1221034240d4498120380103d1f018035400c1016039811580310400c00f403a04040d0002003849000142185000b08001b080d50103040a50224440c0c40c41d00038101d200311458500380103521944202c40c3c0e03500f4414400c0ca10102c1000040a654a03170b603120442400c041418901c1c0081400001c0c00c090f80700003202c0b006040440d4070402400903003415590940d0341c1c98081409442d1002189442c034840003c0c0440c90b28550f4901100036149a046070109842c6044002d120310706000d5081c090600d001c1c14915290090b008000d00e00c7c420700c02d800703569501d599414000302c0039608403810005a000801445140f003040d500198881e841410030054101d0b40c1d003001401c41d03100342c80d00384441e0300000c0e02901c5850031403254800c08034003240c40008809400080748aa0107010401000c2c00808565130a07441d0080c0710740006400e490b40200040845420107541e00c03a401c0c49036001117850001d543c0d6412441c4006c69100c2d400c0a4070118175107040940d40c0c4c07a0350b803107001e41000304202688d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 753468516 1250 753467266 753467269
    0x306060f01230406111f0b040b0909010e010b1005040e071b11040506040e1f060305100504030e010504050d141c020714010804020102060c091903030f02011a150315 72
    0x4450b0b42d0981c2a101d182d88450400d4405450340b1422200c06580d03900c00c10b1481c11201c15081c080f0924140002c012400e0700301400464064440e100806901c880300c84208a030703891055210607110b4076042e0003407058030511024004002c60300241c02d8001081000117110f40303210b0054094000c03c2c0c0b89410020b8034500c10b101d4441161050003100c030241c0e500f12024583c0341c203004842d00141704a80401c4840300303d0f185642e649e84900002024440b004a12810514003944007500458200086d940d014104c0b44000004040403682200410340070902c900c2694400e07010348041d42c0c80982849030f030980d6511013607214512800442154840c44503225042154125000540080c80d00141900e0b4200350714a01c59201d480320a604006030b000c00c000150f031780005d0250300305a0701400d40b640c0e0b400710000300d40e95501824211440c0e03055407400008041c0d10409100400c5555402000a250700312840c000d0740004100340ca80c800e1248000c6101400c84800650b04000a60b111450f6400eaa20 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 753469766 1250 753468516 753468557
    0x3011418040510200a0e031914010c030908070204200c0706020c1002030a11070e0106210c02060a18062f0c06011206020913060f050108060306060f01 66
    0x100c084039207030010f100d00c0e050809180107202c0100e5940c042c034180103108110910090007000251820004031003281081707900c0c14030103c0000c00140070355100c051020306003072100c040620304070642c80d840c080c0612040c5210341704900c84c01d41d0142c51380340351580613000c003c0a400f0b8580303010380e00546840801d00c04198000207000c107a4600c0702800140749856000383c203003921a603200e40901c00e92110144ca66030b020003101c070038615505040300042081081289440355a410003070700e040c038160002c1001c5400040c04078a140d040c07a080e098103142d03000e80109444040d00b255003d644508081202480c0c150000320406008035608500c074083e139100c034003e907200303419030141c1e6402c0d00302d00030200101c022103031400c41020318007145000b90010409585200500c51052441e410074101c1041081540465402c1e10f0001c0c9140c2d054100c495840c001031100303101c0c0b0040001c60300000140c55018220051082d00c006024081980d1580e051081e03c600c01f4010a040003401c000541c9840d0150 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 753471016 1250 753469766 753469771
    0x1205010e010501091a030f070210091b1e030204050711010501090209040c050c15040c030b070827070920030a02070308060f0609010309080c120904050c070803011418 73
    0x40d4110295458400050180041c0340c02100101443c035000c0103110182c0c0003141e0b0040007060401c1c6042d9903180049060201d50601c240c203150600e15101c0902191100040c03d50790b150145a840b81e070b441c2c0010044e0304043c0041000c20030782c3e80341000903140c6540a55400446400d080344c000030210b00c9603003107883c2604207100c201c3e40842d44c1c4e05141041e101e0790640d10054185580340145400303e041d5104944492007400c5488680090100136462030b2401c011a07210300c440080e4140b12201400c41c02c012a8041041408480404461100c9101e05074036580b8240150002c5410401104082c042c4182c0c41001c0c03105042002800281c0c10300110712603803c048005882c0c3c3c88600c1e0040100e84064600c1c9c0c8101444591580b40d0b944107001c031010810242400200c49032545004545800b0b207905829060146040061300040000010115a503040714208007a50300c44e075219049001c2c00c00040c1154030700744014003131800141800d540c0c002000701800c1c01900c40e04040030511004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 753472266 1250 753471016 753471029
    0x20a1506300318260105100f030f0302010b0d0b0415110a05031308030403020d0311030106200f0708210a090b070302010209030a030e040b010e150a030e0f01021e041410120501 77
    0x440305200700c0001d0078811b01d500f03c00111400d07040f040c603280000c00d007101d003404003a090039403010710602018000d500680b094400030304500100841414001219a400c0b10305403036400b2403002580c190841032059004181800340c05030308085038210b0850740b07a0801040881015907505112011500b001c0183d0b100700c3c800e074000c04043c3d0080500900381c0701e40c03000300e98040700280018414240c200000085533440c541c032281c002038002c85400d180c104201c000c81d940e4090158041258540426560410454003a901d08185c500f0071a2240d180305088410b00001c074808000d0041c10310040c020503039140644009810038202000281c1003100911044000c2201c0035030185841c00d0a02600c0356820003420101520707099030700031078030b030043c500c0e400c001c0c041001414034010350180d40902c000804a03001c441082074000c44880c001d60168500300b0b20b41c00004100400c148040b802c86027a00c40202e90001c64101140c180010f0921810008050100c26454040100441e03c502d07802800c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 753473516 1250 753472266 753472319
    0xf0b0309160e01090504061404031e0203120403080910111801020a05070528090c23040b0f040b03150a0b0f0304080307020a1506300318 60
    0x101414100d24208071020284603000854404200d81a41810041e04440c444000440d4943c0d843c6800d41c01058040c0c0d41c4c0c0c2001c10500e0030300c000c1c543e00040391880c48089c00c4802506c1d03210200103030303a01e008000000f180211044001000240304407482908160510103c0d96507822000f4005d065405030402c143e5603082c0803445482c02141e003c070500d820074083c000384c0917025107a02c1302034403100355028940c0030f4103858200012203025001c10310041099078600f42909900c8544440180140340f640200080b00c10108074003400700c0f0400c12404004980d072080c03404c2d140c0b5403600800e800c541025049031000340000500e8071100c0740254401c54600c080701a041380c90204100d042822030700250142c40c000e00100f00c2e6507a240741240c0e041900300003050b46a0761860400c901d0401d08250080124004d400301e140e041d0b82d5a003146003076070780d009020141b03104405080c103c1c840040e140c0c400c1c07801411220b0300c0801c0c05941003c20111107562060103250302c40e0303183c10310459076480e42c00c0c4502d07 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 753474766 1250 753473516 753473521
    0x7060e0a030e030c011d010807020c031b0901050301050f0a05061f05070b01090204080307080702060c1203092a01030b0a1a0c070b0c2509140906060d0201270f0b03 72
    0x140130303c407844925200342000c04480f500e043c00c400c9400181c3d41c486040c0880e00b004902550300801c2418260b4000404480b5418045c1c01c090207900c41840342103005002001c00801c04e46010300600d44128135500084c0b41c01e680e200030b01c0014240103040340780c004c042102e40103407902c00c2c2d01003000304601c0c940700c0c0e950b10700d00c0d4a072100b16160f05030700140748644140824002c5000c040304071001207030400d502586a0f842c2d800081d082c1d2041c5400c10110744215200030500c909028044d511448107030054920b00316020045d03060101000131040c1101c013009210030321540c000d5104168001028203040b40c0a51030b005050140d084824000c0c0e00e40c40007244400504d802040003e015280402200d8100040c01d9005647c440c2e000c240d00048800c140d2810300c0e04c01d5074001c2e440003006054070601c8103c0382c00c0d0a18425001c1580c08811b0b07409007200060241c02d10700182102d142d0b0603035440c0f1803142c036036286900c0e004110480049030f03c11401d0000f04200d03500f005801501f200c1c503507940c2e00e0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 753476016 1250 753474766 753474769
    0xf050a0609150501050102070501230d05011502010c0806090c070614092829040602070215030712020306010905090a050f01120f03051e1611010c0f0807060e0a030e 72
    0x81c103002ea85152418040180034a907404142042195405e091083c1c0c00b4911001881650352104401c1040c1d85000c1140c0015041c1e54002c10b040390710014400c1804034000004034280c0c0ca9002d000000f28240d400070490508203c1c030400e520441031a1001d0801c01680c1c1d40e03000361034001c440707030034951040400d11400000600161340000d00c118000c0360500300021070f410201c45101c60103802460028841c0400700c81c12082400c3c00400300816026924007850700e00d00130f400c50780741a809010300c4100540c050341c0c40d0040324015109900c41c22128008400d512000c0d6000902070303410480d02c00c100240036182d07801c4150143e801000b011850341741108521590303110507800324500c0948031a40c41c001c182e21315101030506816181c0a6030300c00c22100707402c03d0010030182d8541002030014160b00c80000751040c0d400f4040c401c542016001400c14011110b9030124032020b40100b031082c00740000204c40e04000e0400038800d00c4046189482c083c8031074240001010705501060041074140c885 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 753477266 1250 753476016 753476033
    0x30a02070f081b0402090a03052b050a020c0d05010b150d050906070f110106051002010e1203010b1602040906020f0406020d17220b0711070906140d0f050a0609 70
    0x41e151542c0200340c00c801c110b000607121049400040c2c0a03560010b070b4036000e51625400b00001c0c50b08a801c03100382d0380000100403144101108900604042d01c00805c04591044049412904003580100f051495807810004c0102000c24112490366840c9a0000252030304004c051042d0f9843c00859290034900a2103802d8400c01400101150003141c108920542c015001c251066200d14249500c1260b003035040d401014190007442d03204880544216844c6d03415040301030242411015600c03802d41003281c10300070340000e0080d03408959040c00300d5180c40d503140070800c075210f000420100307444580c0d880c0d1104aa00000b004101414001024812560100160605003805241418a07800088051b030b000c2e04000e010444582c141802c85071151400b001d8104801e604219480c649041004001d406c403042c01c412048180240580011501d510380720f04c00445242e001002c0c070300101c00342005150f01031800211980f8a0325030701400483c3c400c000364500c040c0316032000114000c0a0411960 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 753478516 1250 753477266 753477269
    0x2130915060305160b0406050c0708060c090f031c032403050a02011704020d300302041d1b032d0403120e10020d02071e11180106050d020408030a02070f 67
    0x401402d03c200304011703000b4804450449902c1d1800e0350325501200081802d041a90f40655418030410f411321920030300300001005011402c0790f50301c4664501d081419150103861040c0c60041406c540f045d290107020b0340094052a0700300c2c14011141c0e66480551a0314452a041542c95510a0301e02c0360465170007500d0100020400c50700300959103002e41c000744880400707440090007000ca403d04120b041e000000918101c8a0010380c1507085103650030010002e402c43e129409100e82c0d00d19080300780921100c080f50240b030101d00c8010760781c02a0000a007860b4030282540d04010000d9100050360040301084035108a001c0b24034000500301410010032820b0341041d620600d614004a95071102000070350b001c2c0304014540050384603444220b000c00203025507403000c1d0540b01480c40c281f000c8204c5400180303540d4443d44003030744002586018461000703c00d40c020394207202d0030700040c0515070084000d803207460903401000d0700d055210100241141c1080307000c000942e10107074080c0301c8400030414000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 753479766 1250 753478516 753478543
    0x280b09060f180604030e0105092e0c5706031b08060a1206020306030618100e0a060c0509041b0c2006040f08012702130915060305 57
    0x8560400702d20b400754a0780c10243c4014240601c0321040c480b1a400740382030b10403038100201703880300c8032080b0302901c0307895004c0b02e1049992250b2107001c0054140108440a4580e0300303c2d07010340c800c803030f600c00390100c10100080e016000121030546e8031100b100020a070042e803100c1d010301e56414644100c071010001139a08030a05250a002000c91800403e21110b2030002e40c2d8036150909032101c001160b041c07555a044080344040c0040c9990510006400641c0a410207404640346131707448031034a95401e05801d420120319005400c83d00d03100140c9030802039051007a081950024111a078600701201c1801c0009000314074085001c0416107054450b0650400c1e0240380d11610b010403420080c10500d80d03c3c401444d000c01c1c0c140740450140d0783c03000003003442800b40c4072903070340c50700c407000030041480034880c1210b00c1d8280380302d0030940c80300041035041d00c129242c2e000701c9550490f800c00444a0190307022400c9143d50350394040101320064042d104260700400001803103801d5060060500075003c80c0034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 753481016 1250 753479766 753479791
    0xa0b070f0c02270703020403020108100609050d050c130504110a050306011a0405310b03060c031f030b0601020c03070b040b0f0c0105072609280b09060f 67
    0x50032503811800009000794126803220002800b46454440401e1108501107103a01400800008070303010342c02481602e000342c0340c000303071503807030710150036002850f40210300005007900030400041c14280c062025107445441580e42c0c46140f02c000c00c500244150a029604c3d880c1c1c3d0074041804980d45440d60103010503a212081c2500780400710365100c00c10720400303000c60401216070700000c10b4141550060301d4000c0540c1148020307104401c0f16580400e00e210fa84520148211000304c071030744036640c00c11a000d00900925519202d400c9101c2c0c200405401120141c4000c61906200000c1c0038409036200e9110b481103400d10700c0009144c100d8061540c0d0003640071040034801c1c0070702042070300e0840d4141c40741d007a5906584224020f083c0203881040c1620340c01d100601c001c558000e050300c0580c7c0c1525095030301e96810381c2010171a05c4015264030019400c00040d0906c000c040c030118016107400c1c3c01100d0300009140c1c3e507140035142c00700c03901d0340300c1c0e0441001e00001b00c40e0000941d81000901414 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 753482266 1250 753481016 753481037
    0x5011d04020d110111060a02031e071209150f0905071e1a09060d050118060501170a1e0e060f040b130203070e07030203060f0103020c030f07170c0a0b07 67
    0x70a603002c8941401606030340003d240702a4580c460080c0d44400319100d000e5400c82d0401412150181d042659151241410803550300300c0c8400c5900400d114486230340e50030540f0b0102c0c1e001d0343c0080481850603103d40b600d17410482c410003002c2c001c020042010040002d0501c1c840c1c00c025080000a81110071048180215030403000e0740100003400b6960601c40024901c846980c280305140300c0c00c606941c0209012801d0003041a281c0d01031412100c0e24003440c000300750b60741d0070002141c1582c050a030205013120380c003001e40f801d0700c0000741d40f08425100c0001c40c8081d52070b5140d0104036440c1c202c1543c944510144403590010301c5199041102221890310f0340c101941c03400007807103000307020060b036014510414041d5078007041520000c0661120030150341c1000341c00140658002c4400754002d400148400059500c00c0c42180d2091641e2000345045c950309428820b1035038400381044c2e90700003a1000e600002c00f1540c0040c1121508400202010b0a0a16010303041580091021050008000a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 753483516 1250 753482266 753482269
    0xc0f02070503030f2b090f050706050a1d0a030203030f07150e0c01051c1401032a0915031203020a080f0f040303050601050d0504080901180810090302070b070605011d0402 75
    0x1391462150440c0317404444010103290803202900411404c00c4080c02c00c6181400d11007400b0b0080b444500034406e5072a01c5842d428241c0c0e541c49220406000600042800c0340300409e208142450078000500b0708410030fa603600064590703001300100d0140104009414010003288240843d0400c002140a0001d4540c22a4164072807103040c13081070503c02c00141700c0d405a2115401c0c124030780001402004074035400c049041242c1001d0108840e0a0072803110030141c0c1c0101318803021405503540c8061030f41c6003494142d4002c1c01d10018034440c500340440000c00099500003500908034915600161110090b05005143c550040c0035034004103c0c0c081840b0185c005e100555030b003c0d0f01420301007041c3e01c1d0040100c44501c00d00015030b085030714000c14402005100320040880010990720783c806030102d007410502c044400d20640150758802c2c1e41c1c2018880881d001501214001d0050781c880507640d100c43e401d143d2000303800716101540c400c0144101742d40150200d0385000fa46070080501c2c0707003650 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 753484766 1250 753483516 753483547
    0xa17060d0605040f0f0615050f0306040311160e07200a031b021306301104020403140c0406141e0f040e060411010e240d0c0f0207050303 60
    0x120240030075403a80000303400d00c02d44020984209520104c1c07202680e202c1d040c41002400c1a40c0403500c512064000007487d40740c081d420052800f80200603201d40d80325540e00381c0d503030380480c80380351950300880609101440420380c4d00d20081241c182030925034540500018440301a108190941e03007103900c003108111800084044040d81d150400c0750030b24046200c16244c0c010391910083d0700081001000c0d110a400390055000c0340c54503a80341e040b411301c4a90394101042e00c4010614200d44d00076600780410f0304500740e00c0e000074007d00010b2a10f612a203501c41c0c10307820300e154010704c0c0d07000324019100780c01d1500ca45002412101280c12101e0900d50000b13010301400044040c401d45030b8140081544c1e00d03a65002d6200f5070042c001c100915103000c40c16141d020454090b24010a41c08080351306500a12000c988884020201ca00e004046c6070420400061840450740c0510b091040e445207450f03d2207925000b00380341d2166580e608480070000d141c8031a40d0082e81c0039420601441500d1844407 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 753486016 1250 753484766 753484789
    0x50c030a050f16030c0506010b0c0a02011202090a0e0415060b0d02031806090d08011e0303050715050711060a06050901180908040321030c0503060d03230a1706 70
    0x3860201c1c1d42d0b80209034440d0b042c0c01034180d24802c0d05003281401c0205034000901e0a83c80341b280040c1c0b200e80c1c0c1c0c1c07a1a07003029400740d0804083c032504040c491000540c1f00b01100203408081481c014244000380b4003040c206401c64201ea2040015034050100380811500d01c488200041d080c20300c811402c2110080450184107010300c3c4468001c00411144101c21000340083e692007822a0401c0c684040c88941c6c40c44841c219030042106800003003881b600c41c10120001c1580c03481041381c003030700d103070f500711980d40c0302d48810740d910042c0030800c4150b500ca0307001c1c2500442d801e03503031041a03a07009401c1a0601e070000c0c10b01c00c0d02078a4071808008a031a60040141101e0003051800640d070b030010301640140412042c000c042c03510004000c070030010706c20a840c00d071014a1030710407445652014190110380010b55008049041032000031078a1402000c0c4a031203034804e2401e0988086034941d40c00071503413085680b61012201143d40e0001e203030b110180c0881c0c894000a41c0a2a08009001c40c040d4180d0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 753487266 1250 753486016 753486037
    0xb0a09020c0c21010509030a09090b06030c07031202030106020a0b07020f1518070f06170405060126101e140a0515150a030b0604240e0402070f1101050c03 68
    0x140000040851002400f0b4005a01960024451481c0c600091900c0c0da00c8842c80c00f0100e020f0b400045820f09023071045145088001d0305040c80e54071a01c0c4070361615002540304608100001b900036650020707600186008100680061103001d2903450103606002d00100050304641c000d440300c081c40e50001600071036965909600b40ca00751541c9491ba08250003092444070540310f102d10014140c140004244115842a580c44035000d25125092901c11020f40c0d002d41564801030050040004414070300c40d0701141d40000e10700f0b402d0001d61007801c142c072002650ba5219901c4548214107090805140b00c1c0059002c404c0040344101a40d460340004050304c840301c01c03661400007800448200103041c0d81c114004011150720840400a14030329888800340a00190400d102407441781001015074090315404514a50205000c914150340500c01101580070042c500116003100c0d01c540c40281a11707801b88a24040303030b03105803d0904540c140302c0841ca0410008002910300d003007022040e2010b0309103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 753488516 1250 753487266 753487279
    0x39030b09091902190f0e06030616030b04060e010e060108010807120803180105010807080d031b1d060a0c0b061002150405150a1b0f0e060d110d0b0a09020c0c 69
    0x9043c0040b07844000c01c01c10840c4040c0b0315020105503040b1810741d00741242c804031407800b440e99038142459200d8509490080f1400c0c46044641034803030180d0803100707821502030800103c0c2d030358400840c8004402a4000c9114500250030b0100b2542d2020742c4e2405003990200a00f1101c4c0f811203821440d174000040901a140040086080c01c801d03110205012581c80c03000b444196103031003204e0780b10b0703840d84525001c0344030f402000341c0040e02034001c80c8162003a0020306144074607600300c1918803003000c1e8888080313440b190091000ca42d03580e45c0070301401e00713060751601040525031034003100c5c4c40005060726101d02c00c169001c83d4843e5001403042c1c00030040400300201c42e200c510f03040346010300828040600c00061130801042008541c001004208a00700e0703040301303803456601910b40e002e07601101e000107002a01070040500301800104450032240000113485209541466102e81092820108980d256101c44825103000c8036002e000e444041801c52420030381848031660303503015a20081c010b25 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 753489766 1250 753488516 753488563
    0x81c050919021e06040305030c030909090c0907050c01090507081608031306030213030512030f0708070c03031505060d1407022e020904020706271539030b0909 70
    0x31541300542c0c004507440341c01c50b900e03051850f0311310b03480741c105104c041c0c0501710b0304000441c03031040058190b501c64400f400c400130300d0719001c2c0200c03800d0740520601c0c0303095900ea0808e800001e10821008006001c81d1028100008040c0149400341c0000d52052078154018400541c3d20341c10082040102d070b11074240140c0d5800581807100002040d0350000d8080d00036040508492808240254410140401034410b6560f41e680c081d10110030590301c1c4030000e8090403414000034042c2c7e00c114251001106c0d0000c89a59940010700307542d025650718891607880c3c80303080414115801c00c03190042c0150001c2c050b40c50a0031411000d407082c0140300c80d8039500d402c0d0184886c0310644d0466102c1200580155a1000c19082003009070850607400b900e40038a800186186c40420340341c03000026401080c4014100603224410081d20041242403058041d070540c818040072201c106503014407902ca664041c032035034482c010f41240d424102d0180140e81c6202000000c1d68040340e804241141d441100d1540f8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 753491016 1250 753489766 753489769
    0x7080d0f090b0703111903080a05192408030405030708030415031503080f030f16050a030b0316030c061701050f04020a0201141306050c0a1b081c050919021e 69
    0x40e165580000300d000d0707031b100e40d15000b08040e408020030b802901c408030f0580341c4049103011242d0840740c0105880f4176030601d0031030490f02d4214220800c44050904c010354004040460002055031016116900000d02001241002c2c80300c0001032407500c4c05141411300d094a04141c80380500e0000c400c25a6030041e50120004455400000d1a00030442d6034541444569001c1580d00968041d001d1610380c6000070161603101d00c007420909899a01d413030800f4401001034010301000b8a1450349030160740d15640d00c0f03003c441c0702c8034001c600031411444480d1a02314094101c03075803900017126026034a0014021500c400180e40c4081c1c41c19600142c0e90390b0134410803401042700900041095040000380248038042030b0101b81c200707016000402c6151a40148041c10b0f124030743d010404210500c41c1601c0710700984180042c0203005903441c0703140c2051066161035800c458000c0d002074a40d10818041c20308000c0248212110784907040c0391348030000d500050111002d084100c018982d1003080500b45 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 753492266 1250 753491016 753491027
    0x1050a03091b063209030705090f0f0a0506010e120102190f260406020a02100e03070b0f070206010314031605030c010b0a0e0a02072307080d0f090b0703 67
    0x180c0d50003140c2d144018030a2403200c202d1441030310400001070550080c034403800d1301c0740103501100e804103c4504103008640c0c000040c1da401c4441d5680d07050180480006164a500005501c01c480b007072100411880c002028903444000600700c0d4081600e0401000b0f1140d81001071081840c01c04c4941d543c03000042c1c011079019108044110809840b0500d0110069402140c0740030700400a840d801501c1c0700348082c0e03180c003030b4400d965200d50000e40c20205011440d07550050811001910540304840c0c81d000c10300c0c0130313074581460300e01c841d9000041d120107200044513444e42001c11042c149280d403e145600942e504010300001d407c1d04001011090308150130411101c04071070f00c80b4210050344850030000d86a81040701c20b10100d5003840703601d01503858041801400e9500925083e00180c840081e60f070029002200e0448070080c0c0350b07203180c01d10859226a80240307002007004003512401c100ca018108290406454244140103021103116600410310724142c42e042c3c1011904d4569505013102c8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 753493516 1250 753492266 753492281
    0x40b010f290712020a05010c210e0309030303070e030c0405091527010905010b0405102709080910110d080c0f030702030a0e030307020a060c030c0203070602010204090f1a01050a03 79
    0x243d008505000052500843c46a00e8180110020040181c44810564020300b5480a010f6040441088041000200e80c0580121081001102c0c24074402d28040f80c43c503071050f40e40d14003141d50f0b00d050741c0e4646420013141c5849002a035041c05142014401103640d10094090004003003195000078001e0044501d001d8980c1c0000008010000303525001a4020620888161102c1d400c0000e103440d141800d000b124042e012082d8410420b510b021200c0070b0f24190000d45d062a482030b203509642c82032040c00b41e018460f0091410f540c2d965128802c00c400300f5180c0c0513038402c0c00005040002c01d880c001c1521040043d031410042e105031788040200c0c045110300b080247c640303540403040c4240c4950010180103249101d8452a080c50a000200740c1d480c003030808000d610184503038043c40030706d101741c020300042e034801c1c1030820200113035600082c00c24106130070510060f035000c00c0c101701290090054003c6200c03110001c10010031000030100340165030840d818144880000c0c5402014800e920440 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 753494766 1250 753493516 753493523
    0x11090117090109080a0f080123210d030c12140a0b0d02150301050109080a150e010b0a0311010e0d1104051b0c060103021f0f1b06060e040b010f2907 65
    0xaa40301c101c0c1c007006c0d1207200100c1c01a000030380d0110022a01d0244221852a1050800d5800044861802c1044401d4141604241c05109080c551940914040250000280341500c000c100700e10301120052400c80007034034041d4041e061206c0b8100b9a0b40c40c3da2291b8015030034800106d040034050001c41e0365400c0d883c078000e40122610300c0b881184048003020350706850090740d030115456039030108140c0e2064442006040c0c90103d103038901150000d9070000105000d1100049070841c030a00026442c0350781980f0031382e00203c00ba0104151580e120503c203004c01c90491700d001c0c0444040d120091101121080e980c060340c2d442011882c2d01c42c02c00c0d51b003580025a0301441d80e407030b800141c006407200c1c400c2c48103e0095850034025140c1d040380c16280000303200c9035680d4441e00c1000d00d90468230021014a0900100d50b0500900c010a001d0301540010b407503400418401418285080d440ca280140e01c8009144c50b6a4404e100e0354a00070fa000290144c5010311400031008040080001e101d41c1400a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 753496016 1250 753494766 753494783
    0x3010b0a0906090e06011d13050f0604030f0201020f040515070f050703060b180a150b040608160302040503030a030c09170a200a0e1e07090911090117090109 69
    0x9504075080d000300d42603488019040c030150f00c549a5460340c1c0c02080c012015142006552000d20b44505110b0a0744044000f10700c1103c1149034485a003800c00143c3d423014260464010001410380010b03000000014508c002c61404a620072800414003d82c080d40d44110f4a031880382c0408110714042d194000c4e04203d03112070740e140528000da6074240601c02280e03568142040d2000f20f14000240c41341d2600c1c216494851a642c801584000f0200140000501e2252400200f281800700000c2c002400c000e0312005000e040c20a180846034495522000405004010501180d10007000365416202a07082c04202a4580e000075106c00649412280c2c40210110881240303540000b01401c10ba030040c40b841d1080312814080340e9000c089d100007250440842c1e0400c000f4409407900c2981d220800309000c40701c0d00000c000440a8220540fa00c2c000035000d50801c0c0002d48252140c41d00149030380810a00c0c01a1580000e0607100c10120800c040d2a511000100041d80a4002545e21076202040 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 753497266 1250 753496016 753496019
    0x2061b030f190c11041817070212060c1912020712120b060a050705120d0603031b170f0904050a1a03071211191202150a09031103010b0a 60
    0x101000c0d508504260326114590300b0380160460700585403002a660040801c05030540500180b002901c1c64030030900b0011140010312020541001c2250286d19010a410340d44500b10300400c28503010013018211903030440c1c0f081c0300c0c01e101d150302110010007805c00b01e0901002c07007010076550404410288010a0b0002501d001003016241c0c036450016040e0301e5004812031104c480d0310440b0480310006401420421044c0d08250080020306101407140c0201d0313104c01c0c40c0441c0000300760819900d003094039454030030a00400d500902c500307100c6a000760b213001020398151907851440480d2100d0409130b80300042c040604084c000c088401d012805041848581481c0c0f920000800c6d01a8241d070240c440c1e900800b40519000c50024110b034089010071006021985800c2c104080b441112940b00c0f40503000c481040d0788865075040105002607560009151500500c03045a082c00c1c036903050070404000181480d034214403100143d81d0072501c00540140142c002c2030040100ca40340d00c2c1d004451840 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 753498516 1250 753497266 753497287
    0x6020c3a090305101e0c140906070f0605010f080d0203091009050301020c1005060d02011e0302120a020903013b1e030910020d02030307080903070218040b0601021902061b03 76
    0x20400d001c01704130703984440700490403c160040707525441442000580c075007280074010581c000030309a0032500401083c070f0320160780c0e1520080c0300111002c0b00c0a64540c0010415000c201003460010840e0758003428041210290094807880350b41406489240040740c2901074a100d0f02e0075002901c4090300840d076843d0501e100315510303203215680d80003650030400064003c0c104103030150304495040e120301d0700c0c00d0003a5442e121400001c0f460002050360074000000d42e2140151868052008110010f94410219092500f0760704031945506d5001020826a00510008d02400c0001140d0311115446042010080703030030130075002002c6260354146002d010f4038aa0101c02031008000032104020440c02400042c0c3e20b0b491600500c07005608288001040a40503c0903198000b007050300f42c2c7e1800405900007046021107000e107085e5500120200310030810414400d5810030f80900081a040300340d184907050b99142403000901400001c03c0a0650380078050619800740354040c1a00c0d1262404074 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 753499766 1250 753498516 753498521
    0x6222301150c0638030c010f0c110418081206060f04050d060f020a180503011401151101050a0c030b0a050333070c12032f0c0a06020c3a09030510 64
    0x1402288039010340c4000c200f01f503004902005c000e05207601d600d8403500594030b0fa10350503d0341952440d000b036100c0c0c180018180001c901000c0081c450950320b52260700300302808030416402001580299010003800d20700f174888000390340c2141e03401c8565010584c0c8a103003100c0030f8180c9034402c0c42d9060010856410322608248042da2844524a03008606070381c900c00c0500f81d032003180c4a10b80c0600441e0062083d104c020310043c5605402d03050408004600c81c1c4c0311401c45900b100c0c0c81c0b0700d2941d107082c0803941c2e9606000c0c10241800c215040c0741c00504000000b80c6984030125010f8001c2222800e12030b03e0011240301081c5890842c3c80d83c111898202030203046071011500403196041800002c0721207501920441841d6405945415549244100542d2001410203e041007852051144e4100c031003003000003641c0544181400350700c0350201503441c1c1c03500c20600b031014400416002c00345040b030020582103054195809085003d22401c400c1075401003600d4002900341d00503000704460000068 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 753501016 1250 753499766 753499871
    0x2d1d0705010f022a060f0c06071101020913051e04140609070e010b13030b0907030516050d170405120c0906010309080306222301150c06 60
    0x1e03200c60300c0c5540900c10032030312444150b240003a480b10140410104c0f42c56441414182e04000e06440c0c03500d07070341840700e009540104011052030385c803100801c580c2d03d61124a601074015032800075030800141a0024011445554000500c0742d50344e00020591440000e1900c03040307044043c5080d0b981803a040151200c1203114016a0501c540004141050303c0001c0c0b4408850b5403900e640c07816400e020819410380d01000080c3c0c44103861100c048082900702640d070f80a5102c01c80185082451803902034209401800d5041d40e0b004032480c200100c0d1100c40c58000c0041c0d12214001250803800320b601171900407a0441500f1902140c1c00810590000801c166881000c5500c0b101940e45c0c8070046061380d0903000c0040042d44c0500200d0341a0070f0001007008118000900e00300131040320700d400d90868403c036410303c0803030b051501d450407a40e000100c080e01401e0082500144441d060318041e0810104c428010580e030b941d06c81d114888075010504402c0701d1220b00005451000181c15100400c220 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 753502266 1250 753501016 753501019
    0x10302190b0a110309040606030e10230604020706020a120e0d050a0e0a08060c070312020a1b080702041433120703140f070602012d1d0705 61
    0x30250400094a508a034510868090071010303468030110b86001c98400c440030341c48224512090200d10041d941d01c2c0900b40113402c05540001e42c0d2004c08401c4c07850400c1e810002c250061500680094106200e042c00071030b0ba42051048000e901c1c0c3c40702150082c030030a0000750041c0e10104160112030f0348a140ca05e0f00e10401c500c14401c10151100340c41c1c8031014108000003141d4200540500300e402500000003040c8018010b24140da0b80f1100380c1d0a00c203045400d07011214002a10604140e080400803449540640341182408400800680742c44002c03901c1c44400303070480d44ca0000b04075841044581c66a806030042c85008042d14400b210100181c85900790512241616001c0380d0007140242e44101c04001504244103850090003501c0003041c0c4000305030300940384007001060380c0280c3c41c004001c89800515038051451041d130b06180c641e40103a011039040c40b0030000c0c0558684522400c0c0700d2410050b26040100d1182d0a0041c00c681c4150b651019a094402c1c400242c00314490048600 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 753503516 1250 753502266 753502279
    0x110c10180f05010e01030506060d0603050304260714310b0d0f020906060403050a0b04021f140f0405042c03130e040503120c0304020319020603040308072303010302 72
    0x200ca5480c525180c1040c040c2c00d000544003802c0b03200d298481d801050700400054019840d00054850720000d80d0340c10f0f002600c00b640002410041c0d46850507000c46c0070300404ca4114500c02800103400c1c0c56660718403a80840c9000200c4c04001070f5129598024000c40c041c04001c400881200c0301c4002c1c00c2012000040d961500d1160341290805807140701c0244d50020307680103491003503030800140c3d403005031240e504100c0a100100000790104482031400d809451607044514041c41084903e16107001d9410100d81e190072148080c03a0000c0004601c8800500410f485280d0015100010f0081e0787c40306620a0030502c9050501290700c55002c440c1c4100c508400600c03c0358800c0a542e4410fa001d46850180d40c01020001500c011142c10703007041c414415603250180400c0c24001840c0306581c50320340c00134004144800c600e0308201003a00320a521068640c80312207500024814040244060280305a0000194000f40b284c00403c0040010540134550156031030a005095002400124003811 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 753504766 1250 753503516 753503519
    0x1a1e030a0b1f0b0a120b031617070509040303020f07120f020d02060702030a1101112106150a08040222140606090307060f0306120605090c040b060406110c1018 70
    0x1600001c100300fa200c968100510300074a0180845088800c4d80b07801221541d2000c2c44000380c0e900b80686090906a200a00090b44c04c1c40c812003c1200d19819140301544212001c001a44500702d0070743d8000d4140c100140c888035002800d0b001071083c200002c140082203886007110f01d401010035000031484d07908680c840e600c3d0704d805a96400094071005d0150b801403000d0302c0d8040c0700c0c0740944500b060182c00403c050144000300b09881e00404005108200340c1c214001000180c48a442e0b4000da084034158640c03403018051080c5031050b120403108210318500020195100c0b040a070703003195411100c56100c00400c454640c01405c40e60113001d560150000420020b2030014156000c101c0000d024100032890141d00392061100840c0000c203043e142c2030002940c5803041080e60b6002c0c050500481c2501c5c0c0304020783d040a2032038680500ca64a0001c14202ca0b442c1c2c88240c50645041e8184164400d14020041c0c1c5080c62319140d00d64016176894a035900540e01c8010f07000c2802c03500001c551900d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 753506016 1250 753504766 753504811
    0x906060e180601050f120312061008040c05010e03010b0d06020903010605011103040504091406090c010813230a020303030a090201080c030f0a1104170a030e041a1e030a0b 75
    0x11200200c40d410035030240b00103000914140d4001c80030a48000d0205034001800360030300341580c00c100d039400c9001c40f0010400c40307507090a0000e026690001d00d0252254038042e5a41072411000e0302030030381040400d044035112501d00b5481002a10310050030401d1200b42c13880c048000e54080e0801074065400c2c040001001e50103a0150201002c045019504090400062000a05c551441516000010010b80e07040c21410700c0500d028404481c081c003504501d0400150480310058054003076074207400d01c110045031244005a11245c1d00202c81001c403100000c106140155420000e0343c54040042485041080c6500001c01c50780300303032070380791080d42e4580c1140340c2400100c84840741251100d0000d40b101c2d00d15403105d100241011b8409043c147c80d6041c1c4244014003221280035503101180c52002c2c181c0100c000640c880d03003200d0074072200c08481010301c0005190b610550242000c12001c940a0301c80100c59200004045c003140e0a2012a0502c0e00c0a0340080c0c48140c0e01192f10903080d1081d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 753507266 1250 753506016 753506041
    0xa120e0402130302060309071a040905010b040b16060615090f0f06081522050711070f03031112130303030c0302160b041a091e0d1b150906060e 63
    0x5102e03200704201295440e580901a455000410507200d0740103100004c07aa041c200d00c54442550501441107803038034188a080c0003110010b821070005800248020415070440a04461070710001d0942e00c5440c80750780c50000003901464200ca4402c0501401c85615141c0c0000c122048880314141c1c44031003584c400710300481c0041f60040d80b0010b80010006400ba03444070940c0504000007400030410300c800000e8200d0300b03035081c2c02e26164645d181c038144542a64082c1174140304441001c00740007402c4c501440360b00014200e220040034403001410000c0700f58000c0c850448a00da0041150340c0c1d81000b036a54202440d030740d010440110340f5085020000b107200f4420f4640403a1100c41220040f80310f51111040ca0000910031117110160780d190807411400c0500c06c50007416624002c00f240440c2070014115203a10710141300340b56100509000000794030403910070054420394220142030111f82040036050800400035408682804407070400c00c803c541c0210210741b810590a8001c1c1ca4000e0781555 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 753508516 1250 753507266 753507277
    0x30f0703030f050402090612070302030d05030a0e0627030d0f06030308100f1404020d0c021b0d0c14061b0c10050c2d160f05010527060c0a120e0402 65
    0x4201b480b1100140d41c5007845a0f10200c0110403e040314a0030343d5983c00a0300d0301c0300181c40c980001d42c0100078064448014040c2c810034543d04000b07480285001c1d441c40b11255030141a200899495252000b42c0365028003c981c80c412070130005010984840c4c031040301404040c401100007541e90b0b00042c401d178024903081c00580b040c0e259182981450b200ca507104201c10007440d25031250b4200000030800c3e0a80c440e004040e460703a000760001000c1090582036000300b0708102070182c034920030100c00103048500d08000b55201c0c140070749058502500401c0003400b49441c03049000c46450b441005603c00005d03c0000d0410480d10f400361400198401c641d10301032440b011141d079100b0100c1945285801e858041503160850340c0300310140b413169116280102000d140c62480c84602014030004060030b48501c05003d003802c0c41c62601c2d030140111008401c0442c03000720340000c55540040f4586d00e2004646081520404480c44000d82c2d0134529000b82203039001001080521640c4000f81c100f500030b072003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 753509766 1250 753508516 753508519
    0x30a050f1203011503020d270501050c0c100c0207150c050d0c120c02060f160213090503041a0f0301140405070f0527100203120609102105030f0703030f050402 70
    0x4140c400c088005d80280d000b805a0703012540c1c0300c0000e41c0c82d85424242e14007140d445030841c100350b00d28a05210342103d10152000c51b00f480200821510303001d0004440104014000e40007800350b40c9a0801c900f810956004017006400e812a00c490f09503104400585550096082c3c60101d1b54000d81036441c0001000c0040400b518402e4102405002d007049801c5580040c0003d46411190600e21030194803100b060322002251490301015820007007124504402948010800c481c1160ac45035601e00070303840b0340204504000c014101d10702182e8140c505000706804040c4d281d5844500b920b0240c103081000c00c2c081c40ca0000050020b521684104200e40165182e40e0302d4100d41c00351039010401d4942800421241e4295900d4490716220450106c080550740a0341d1203000c048960b1040400c040c0119205203124014402c00d0101000400211000c01c44c0c540f401640c0e400d144050380305880740180440c04045100710b00c01000400400b1128400c1c1c0c1c2c20010342505000c070400712117054401070b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 753511016 1250 753509766 753509789
    0x51008180d110c0f1807090b04180f0b010816030608030706020307030b10200304081603030216050a150e0310060f0f03200a0b0a03020a030605040e060c0a090302030a050f120301 78
    0x1034485c4500c42c2025504041640b404031206a21032000c0b10f000e0b13000d03600c25924002c0045160524070000d10030251803404000d014000c0324000030000701644000380051410160340c403800c4090b58000c3c0c2c081801803a40100350f0b42c4501e124100036000b50001c6480c18046414400e01c05010703d441d290031000405251980d142c55010006040c3c039641103400b60111503c410000400c81c41d20801418100e0728001880030015429460028240b6805050804800980240c107019595603005c510090341d40086100c05040b002c0d181c101d851050720005503800d400350030500f00c6c1b029035a802102c00e0b250344414038280c4a07556020321114444e144409481d484483c1c0d8030100c000c0d0040c032220100d843c01007459059a4a030102c07082654408003000303010940c005103418801307805004443c021303c3c040341d040159046855a407a190b1000800017002c03004006003160080d40590f842c54051500502110001e0020b850100c0c0e9a2088a81440c0c41d889004455402448004122410b0310301d2100c41 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 753512266 1250 753511016 753511039
    0x132306010806031b2101021b0a12080703110c0c030d020f1005060a0315050a0f0c0c020409140f030301030611070c0e0601050f0d0b0103060e01051008180d110c0f 71
    0x2401c0410b03841500b1070307807203550403105407005c446400f034151540350440001a0703038014500c901d510700e40d0082c80b41e040c43e80207200c1a102084c200c0d54078840003041c50901011542e10f21404038020700090740030740030340354010526042e4954002441c4850f0f01c402e50407141940c45004081c2da03074101204507030b415540090150501038545410003500f1010240c6000241a1290b84141c1c43c5402da990143c40e9565a4040012040c19802181c0c200300414130200706c008100c01000301501e01e00381c1d020703026944484604003000719043d41d01f8200c000250561707800000c2000655101d9000384810368005081c102e040e81d907242a4012220724561290381e02c020303203140c0104950702d408000c18840c1400010b0104480c605030450050101d0300c1a2180000c40104071800982103400c150806400380c00510014045600c40380d40107840c03007401d4246008569184444540742100d60002c600540c05807001c00356205411003204c004030900202a01c00480f980700602c0030f031506c084419544020203480 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 753513516 1250 753512266 753512293
    0x4050606042909041b03200304082d07020102211b0f0d0903140a120309050a060e330a0c0c0c0e060a08030c0703030e13230601080603 59
    0x640e1010700d00742d8440c290604680000140131104a04c11440014410500c0d9000440d0f06100b52542084842203005c40340031901c04c0c40486000062009109610010300409100315582a0390002684055802c0c100038001403c0501500076080480c05071240190800d0007003c03000040050030781c2441795504020722100700d00116100035545000c103004401d64070940d43c009228010031114280c46080c0301034514034203200b04108200c00d091540e0007000303201c0001008201070516000c1103240c08a1240d800341802070502e1140c032801440c0b1880c04081340d60804011074191482c1000c0003416492158100c45001c45280001c20343d421402c683e80024940340d05548443d00b07403555454074400007040b5946581d00d1803c40e403c882c030480c1f9110108031161030000000030241c4180c80c040c9d400c0a8519412503502d04241c0402014448440c41ea0f02c01500c030820000944030254109010a000340c01c160313610107043c1c1010941d259004800181194001d486607030042c1c00150080907024402c41 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 753514766 1250 753513516 753513569
    0x3020f04180c03120f02010b030607031112151215010303081902120108120903072c0a0501060207060e030a030e0f03100f06150c06020f04090908090405060604 70
    0xc02540c12001c0c4507804000b0a252559600c041c6115200003c005030704000302815111001d1600800c5a050455170b800d1900e0108815800200d035080224100f8101c00e411134160242041d21640800300c00200050a02084e03040107940300141c81c051254681c2000594803016440000004000d1910040000911505000340d101c0101e450498a044503d584003081e81d01000c1320381c076101001070041c402000c4c02e0000609144000320010702e4000740d0004607407a0740c10362103480304200d0010819545101c498001c0302e54030300f41030014207161518203100002000c0a004490042c442d01001080a43c0108100030060200030000c201e405050b1307400300c60400301880b50780d40080741e18040055545040102d44084105510081490701482d008c000c02c0312001d501030b01134203068195207000c40b5000500248030a400c42c50150f554014015089401c0c81698000b031190351500380707054244030341d42d000341c401e0b031030f00301c40502c0262548400c1100b0740c0a18000c0040440024481c0030000c0e0341d00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 753516016 1250 753514766 753514781
    0x30803071e05030603010b0109050a0b090d0c060807020f03040b030f040302070b03240303040e040b0702150f070f0e010503010506070309030611070c2c040614040c08010c0903020f04 80
    0x207140150100030342040c0c1c00e030540c0740e15140070003051010041c04031926080c040c95808503000e20300307002258503000c0046d10303c603814410b0700748200d00080c02c034640351641500f040304142c000390b602d407a03a03544d0000105103c00440d1a90014000c54281015480d404000ca904640c0c1c0303051500d042d500c88900165031048084c0089080d44908040091112041005188114820040b1102c42520320842031a01082c5c910610321a400c100401d0116009a030703680f5401541140310307000107690b0013130183d203070514000641101b4040402017002c0080305100d414401d540300d540d0100003140c01041907030b002c14489016404154107200501190603c0d8000c0c0440710300915201342e403a41c1e2511880c00b00c030030b00c1d80d0305c90070300b140010300100340216420b41f40010444103d03444561000c070b0b030165105090026401c0818030440c404507040c4049600090780b212150a0035512a080c0751400300545c0d00f144c45400d006500f4001000c860500400401c001c681c0c000c1c00341214815000100001030850 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 753517266 1250 753516016 753516031
    0x6060a060f020a0629010c120c081204050c1f0c03082a0406110d020703031803211d03030d05040305131710111204030203040b3c04030803 61
    0x4183c403800c0803502d14054003c0c001c02020120f0703180300000750108030504150600505010051031b480000600002c1d05000c209041d1410383e503d4500c40c80c2040a0784114416031200380c400c042804144403005c199425a01d6045070790f403400700c65141554038400c4000074508085105c0348124404640130303001c11350340f04100112070101c503100402c101c0320740b2048113240c00451001103400d014441e0030264603008882401c000f400c100c01c4e030100003540e48546000c000c0401003095001014548801e000703c02956101f14501040080700440008444001001da80001e680485094103e90b0790000100b0720780004e00950f180103e114800409031001410440400c9802c10000d2600c801e80d0b00e09001038001c480500321179004045406160807400035103405107600d481641c006046c484d0003180d10f003440160102500daa6141030507401c5000310340c007980f0344031000030307107201c0300c1c542c07264a030041060949940d58075400c44000c004810501507074001103814204014004940c1d80006983d10080 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 753518516 1250 753517266 753517273
    0xf090212060712051315113f0a0b0d1401021c06050a030609140a0b040b0919030e040f0c03060f08030a140c0f030f07110d21030b0a0b1b06060a060f02 66
    0x81442d1f400b0300da90041944800e00364241c00c403003400c0c001828010003400788088440c00c408091030745040c403410001d0301810f20a80d6a1074200c03010340b500c08406104540140102165100300c000f40c501035171101c80c0395039200a0860000e0f090465900c00c0d0011382c2c4000d042011100c0c00c4d651080000d0884c000161814900540c1306208102d0402c0102e04031880f031040c50034103091502d000d00700148050a50700d03160b00644a0503540710010041000c0207a05032402d1803080c49000c003c10700030702064541c42c0645060102c401a10340d0181c000d2421146851030704182c003565488019240d005031081d090000341080007181000310640c0103403c0b00085003044c0d8a04100500310140755502050307140c0008103010980a080c001c8040d212280c2c0c02c0e050300e490280d19090794032a000e001c1c128015404181c1c00c2e01550301d500e07210b50f1040319080000340c820480151100030f0300c15981c029198102c166154420005015040400c01c03901a1001501f09104c03203007442400c0d0b419541c0c02172001e04520 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 753519766 1250 753518516 753518531
    0x6010c1212060509070906020d05090f0904060e0106080f280222050103050109060f05070e060a032436110c16060905100504090f090212060712051315 66
    0x944030400e007402140f20b034403034103445450008043e0408070f03409c580409111060000e0149504c40c032800440c103450464290350b081d0b0791840c154000303051440c10501250318007000850701210014200410540c0e400840c0c2d002d603034404000000313013204c1e403a414000417012409001030404021707104000f41000000c13a41207646100c00801c40c0d0090b801520b941c4c2d1228015800c0c000144500b024a60341124103000b54a021003015100e02d9001303003207500540c40001e10285c6180710394054103900026a44001c5414010441803d001c9100e0180700402031400c1c10300a540e0b94a01c0003a009464060349049014203029283c20040460190001c001a41005880d40e207440c24071165145882c082c4003008518103104008000300190b4100b640035071104a200c0c0714143e00311050b2411120211000b0078400301c13085100300988207900d4020340001460340c0050141c0c00c04201544110120b9440c80032200480d1103a4040e03900a1315003e480b1003141c0c1e100d42c00314040362614640d080301038101042e4038 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 753521016 1250 753519766 753519769
    0x1e060903030f0a020304050f0405040816020102010f0e0606190e01230a03060912110307021201060506130e0a09030f030b0102151f0e04111c0204050406020301080606010c12120605 79
    0x1a070103c4012001a040020240500c0c50201e00d0000c1c200010388081210746461750746c15060344a41c43c91183d08410000c14001168400d4000300f035007080e08101400710710341c1e0402c265503aa005982c5248a0b8544522455160300c0e098803440841d84541a0034006034645840001d198103203a1804141070000c5411001c0c88e16800ba225008500c00c10300002d070103a05003482c8241c1d500f2007903204100702d40c410301500303200800021b0764012a01240ca02d080aa01480740600615482c2c0c8007903002003010944000c4030354201820400c03200303c19030b03001b0f040da91a442c10003151041d01009000c0f4560b49c5da0a00901e02c80e61021080c54410700455890380181c00c100000f005027261207001031030301280903000f50341c10060303084001d01441d2070844507420255034005004920302c14850081c04c038070511004012401c4a0b800b5400d030050000c000609003030528102a500034083e02d0001d104410209000754481c1604c41641e6030408164032000d1408102240c40070405440710542c940c641c07102250320b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 753522266 1250 753521016 753521047
    0x306280e240306041115190206042303070b070537090506040e04020d1a0103061b021e2103060102010b0a030f080912010e0a111e06090303 61
    0x900041108141c0011410040741960120800d24a0282d0401401c1c000010b9004030700300444d80c0d04940c0c1140c0820816032042190080343c2c1001801e904001103004416000b140e603038041c034050210a0018070780e42d280441d50b0700701a41e00c40c426610402c07124000c11406106190403801d00d2910b81d15107a00020001a51070002c01d1a142941c43c0c412540301d41156801c01c0380704003a4509180c070b070052400000540c030f4000c40c85400302c03c1030071000150841d40c0340342c00f901c08142e0018051b5046118401406285102400205c1d0080c1c43c010109103164010304250111000e01c0c0e0080611411101d8605a145000611800c03507100344e043c0307140e20252902d0348040301e6007000a01510703846c2c0407000a082d140003030407882c02440da04e0000c0c408988072070020280c01d074100c14415510301034480401d80e8510010840280c070351a080f003502d40c1c0f1078042003d072100c501413030740c1281c04580a0104401c0070311408007912101c04800f849150b070705041019180f91140182680c1c00c21403007841103c003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 753523516 1250 753522266 753522271
    0x3180302101a15090301060f0f08071d0402010e0103060b070308100b0a02151902041e05010806030c040504050f010212071b020d0303020310050415030b09030306280e 73
    0x5600196440800c0500c188507009040e1015000c0460a509080c04240d00d01d031000071011040f4000100e14031a074409420000003010803001e86c8404aaa58481c100c0d500315038007441c0c0740781c018800d001036840310781c10a6010b04805602c0420094543e94015125420400c00d46414143c440c07100040ea90030304070242000034000d4458150346d15021001e00c41034802c035004040d5580c4140314400c0015030000fa890111006130281020a4403081401a40783c14481c2000000030300001c0c01180c040070b88104412800d4501907401d04903611400150782c6003408842181c0c0690140b05400b00d11f18290300050f801500900030398034203008425510342a40e001d0300700300c3c0320000c004060280881d031018202124048580b07842c2d0801515900080e44003c1c0580301404040e00072010800000744034207114014100104204200480c40c3c441c0d82c0071a216100a54900c1800750004121038000700440b4400c0034000d00b1246540401011400c5c015148914034440309484040841c244118603103503070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 753524766 1250 753523516 753523523
    0xe031501121a0708041502090303130303260a0207020105071e0309060c050d030b0f04320405070501050313080703090e2404051315060e0609070e0f010318 68
    0x20754000c9607090034042803010459000202c00480200460b0390b500c401055006a40104002880c1e0003e0540c2806400380c0782c1c040350325000002c5c9140700d81005111000403607129803a014464001d500e1842607800341c3c140000c00301560040010540d550640c0200320701441414818102103903a00d810502da409003c03d2400624075102090034942c00c40e101d20000c282a02c0c0806100b00240c1d00c4585541655103910241603c07070014101a5403915403200304244007810402c41d039540e01d600800150301500c020041d010402d03400c0520440f501b02400e105070340100040401d00d141000444407031b48003c040264844c6c0034954840050555002061114000e0341c503c1c901508011200004101c054082c59901d0f08900280d040c401b450340324895207000846001a4a0740c50302e00c0d110065401000003031004244005500108185070300c00005e032840b10446059030396a060a0140c443e00075101e000210345640d1400c3c4062a00400e058003106040c507012504144502e03100107003049180048 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 753526016 1250 753524766 753524789
    0x2040e0a020d050123130b0306090706031803021c02071a03090105070e0f0906060d110c0105010906180b0105070807050606120c010e0909030c07170705040b100e031501 74
    0x2e804040380281800342881c4c07880c0102a2184900b40b184c000800742046001c1c01c00781d544004d420802c0c2d80405518a80541912900e150200c0c036180c070b46090740030303407008a841c00d81d40711101e88080040e800ca41d5410380082042016000c0496440c10000101c84114802c2c148086040c02400402d079884611031415642c0301c0c100310320724609440000f4141d03000c00c01c00c118a20789660350b4004c5030286600a070b0b040e4a15803144004102c2c64070030001c2d07010909d03040000700a051128800108000001c0400820043c2d89038a404c0041d2145071003003810400e80c0062505940a0981c0700c1c8502540504140b45495880e950711941508111015907483d04103108010386824070580d1056620b1001000d021204140300000c0c01d6103d030302c020140203240d1500020320300c640800494844c451654200e1f080c01765036040b01c4842442c1a40c441100340907681c4c001440c1d040a006110311182d004005034010013560500322242d204018070303281c0c54400c0c9404041108040300405029001c0417403007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 753527266 1250 753526016 753526027
    0x712050d091a03040b0601020a020306190b06040807170a122708060114040b0d060b01200c090a021606230603120c07030b27010203060f040e0102040e0a02 68
    0x942111410b80c450b90301181d5841c000400d4661110440b41c1c0b2613440701c00c4030140d80f86e03000102c0c072301030710705000a4040c4120300510400d011215880449814804014421800c031201405141e004a1044648076402070030148001c2d0f403904001c4160840c0281164070801140c1c0355034441e4502c0b0785004001ca00c4092410901c17040143c140c1c1a18042916202c0170070340345c4040603680c2c0e0b0341440361044264030f40413080d41c95a10b94000c20703842000249090072180e45403c1160042c80c803055172901042501d03c5564107002c419081e81d9135100c1217030141c1a0620b12070144640510010004d004980c0d00300503c401c0d00092070244808103028800024250804c4e00c020140003122a59a24551000c181040a544da0001e100c0300d50451441016403600494001e00f072070701c0c5c80c503000148054040810809403200c5070f001040380c0640150100800da591402c0b1340e00300c2c40b040c1c1c1e1894002a40d2440c50145e41810380010150719290000189065510815241c00d284151580307040385400180 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 753528516 1250 753527266 753527293
    0x60e010501030504020d080f0f0315040c0215040215120411090604200a0c020a03080c010b0406030320160807181b11030910031409070810020c071205 66
    0x15000d054207090800090829800194414001e118001e050460000c1c2c18111020f6034000d0750001100c00d141e19441c0e080c04411201900c1140c050b0a000b07a150401d58090300e0f10002d89000b0500c02c04607810703405c1d11950244440340002400f88007a00000700032480401d655000b00c1842a806580c12807014026402000070b20035002d000c0c2803080d404c20003123112481f400e01048804000c1b03502c00d075aa0b002044001d42c2d86200040020f94032841c80f080000a2083d04401803800a0264000304500020a010013088842502025001071b813403040032071b610714103015001201118082141c0c119003106881c014400d00c140c1042e07070745800c01d00003000032480c4145c01e03000102c842e043c180b0074202140812001c0740c00c406817034001c02082800c485110002407040384c6007240080d08030712456400c200c008d00508803003a01d413031850410200240400b80d010034401d040d02d0680c000750005039111072100b4040d411050742c8141c1400f8000c1c0004501d8034503138010b002a8070800150220281281c1d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 753529766 1250 753528516 753528539
    0xc020102010c0f02030a03020903010e190c0b1201230a080f070504230703020c010c0e120a0507140406090c0e1806012c0d03031e1107021c08030a06 65
    0x10902c000740039800c80615092070300401a01c1c8801041e00d00140c4840b00900040e0160804482c0c55036503009200c0000c0070542c005507641055402198003861141d961914a04940304261014145180000040c00088036203641481c842141055125102400e040020301840c4258080c45460b03000203048045403c0c10b202c14070041c00101c404011111518084030001718288a10f03051081c00c407800540080d00a6042d18024112075000b0032800040b001c0141c0480340b0880c4a5205440d10f0782206000400080c010006641c40000340c901d007403038903031012403035a042d00403181d10903152080800d1000035446000c0160b81c1d180e80e00d0b4120070600e8140301149929110b4081c0c40783c0721100300320050740c00c0210b0303411101c003042d44c8002103070114031036048da248151281d0354881008942e00c070070305905030032100c0c010344403aa0b0031a840e0f051070b8454044500e0849130040c003040c10311200015140ca03d50200740903000c4400c11a40b002e441d41c4034009540200d520700c55040c1e40f0102801420402d1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 753531016 1250 753529766 753529781
    0x90909060f05090115051905040c090914010e0112050c19090f140c070512090406150f020f01060807030b15030303011203031406030303160306080f070510020303040308131a070c02010201 82
    0x42d01c8140e07034036505070074003d40b02100c0d00a42e030103039444442b84944284101140c00041008850030440c40c2181c544040c0601c1082c0715020042c44c660b000401c420075616404040c056014001b88001102c40d420300080c1b00f40c0010186660040040c0001c0c10395407030003140c004008107800014940e804c290300074000403016080ba400c515050001c00700141c800600050f91242000700d60f6100e500c007000080140c011f43e04548600303000302c401e0010160304540e80c2c141c000301e241c007552041401e03244c5c200e00702d424500c1204419800300e40b080011500000c00d580d0007403000d440002103015401c0210345540e2003070388101c0401d030301ea03c4a407061543c0742c17241e80390420181017110094146880080e507070b4000034144060605c800208010b041c2e019902843c020100303101a1520103c103a1481a02e840d0b107481910f0044d1030030308010340d10b540701000f10791103640d040d12283c906448824021080712a2403204551000840e10300c62000e543c512041c5110705819612440380d0003192000a0075981c40 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 753532266 1250 753531016 753531019
    0xf100501180509061519060c0c0608090c090402040b03070305061506040f062f07090e010606050a14070c0f03060c020f03300903030912040501090909060f0509011505 73
    0x141001e0008907480803451039045141e8508410050250200083d00d0420100020ba00c004038034400087c203a402a201502c80c600070404a103c443e5180c0c400d481c208c60403900200780760003c11110300395282c1070451039001400a0000106c0110034000f091800d02150000c3e00e06600a0b010071800000c9074808500040082c0c0d059400d00d4a4407841119a803601d0081005010b254203400002c1841e03051620109002000d100030b44035112840162070b42c41c0c600a0085007410300d90316124110701401200201c0e04a40e6802380b80100ca0601180c01800c4494078111000c010085d207008280c454203d100507180106e21000a2459850820101d80c40d012012040d50007090007049040c0010080ea840c0050340402e14a0901d80c001400d000c040301800d002c5400c08a800c180401610000003442c4200d02c040200d462a000d601542600e40c0528440c20780007842ca140284000002034018411070361041d18007040b081d411074035460945100312100c0c1d5840c0e54070141c001c9541d2070b010316000104070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 753533516 1250 753532266 753532271
    0x90309210106141309050c100329010e01020105060d0b07020f0f0318030105070e01030b04141306050112080915120a0f060b040b0417030909041203050f060306070f020f10050118 78
    0x340c96441355107031f01081c044076120300c14803102108810b011380c102d040c400901004503844068100700c40741120300e684008500049a040004005500501c1403a0103008001c210445112007a40c903000300c0c00004149000f1030040d15900c10a1f00002c0025034120020a400b40d512184484403060400c0700c3ca0a900b84a80c1c10a420310a107140c00c220100c00226003860041100391400780820080c0154a58401c2c0482c44641080401c40c4900500303540140706034028007260f60b07510204145910742d414054809e1804100c0d0820b40d141100d0401c031071180e03101c3c015085c03e00c82c0c0310a1400e083c04548200500e500e03402442c811070028411200540318030035156007898100307980030015001718003440c40c0d85038070002d11103060041001030f20745016000304084240d10709480d10240140c242c4142c400840e0421000c26000072801c0360741c074800c40c0003034001c24140c0d40d6041c0032a030406442007a0350a6005041c0c10780142c50b41808101c0c0c00b408454400701d65549003040825011a8254600c13010301d1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 753534766 1250 753533516 753533531
    0x90d1205010e0a051f0f090b0a05100513031a040309210f1b032402040612090317161b0c0e0703110301150809060903092101061413 58
    0x5051079519a0443d0030100c0001d0315540e103607015006400540f0041100c5524401d0004181281d00360b51010b461404e003041c800d8108041c103100d443c0c011805529400860409210b000f10700c00c3d8003620840614842c109025556601d6114510400ca43d04200c6403001004010505400c900c045005044030001c2c2d145c1407107c82e0b218503404a2800d4002c204801c0100b1510a00681c50880f81c01040d1035040cd00c003081e983d15103030009810020145112410054294010210324400d4404480c1681c0f2801404110a1140c40c0246142c131380440500800082340c144049400107014414095100700b42401802c1d1403000e00603070300700004081c18801e181c034410700003191000a80f04031380c080c40c007500c1c0903141d0400c2078018045202c480c03042c1503004400001c2031020541c085a8529954036004c503140c0b074440203a5100d11017292080d041350300c20407498126082002a04c019404402400d40b8154080c046031425101c0079071051142001c0c0001102a0345000080e00c090209800d1041001c030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 753536016 1250 753534766 753534779
    0x10b0117071103070b0a060807060c0f1518032601030f060507021f020a0e010c0b0606090f130504020f0603190b0409021306090510030f080705030c06090d120501 71
    0x40009041e0810022207040500501008105943c1c0e41503104503469003503c1c0200c00310006141c58407900381c81e449860130000d151405002c0c604000d0350032140000e48003125480c0d01c041c010118601800300ca5450f6070400c2200b0b66100a003804038401d5aa00013046280d0202911041301c03a5084008600218010800180464030300c10000e54000760115031907071000010b03420b000070401000002006120183d40304030b815401031541c0005034582c0c00300c072445607004460441c03ca81d4020413a41040c4045032141c94038001a10f10048000c100e58406015000421083e100e402d0005640315102c4052004520b4131482c100e200d10000d40b101400c500d00b08d100200200720019080522603a9071620700d140c1d899035017180803940d07005080b9400907440f0180c00001007900e8403d02080510380808610480c03c000100401c5070780000c00c00c000c2001988604546034004882150399100800c0740c0e040170b070014001984070b800c103e8044d081280701a00003420f1820050410303600d441c982801402003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 753537266 1250 753536016 753536057
    0x32a0303150b0405040f020c0a0803010303021203010b0306010c05010b040204030c0504050a020a02191e081209030315040f200c01051332030d02090a12020f1009030c0f08010b01 78
    0x115039040b0f0340072501340d20059006002380300b06200f808050007640c0072030090140c107100540c1201d12030750890342041490030800400d40001c1c040c0800070788003000401e15561003040341d200d101d40075900004100500740005000c0380e001e540116034004034048104060314062082a80c00388665074250301d0f00207400002504c0300103020f0b42c2c001c400d007a0a080d030140450441c0b00c6045c20031a8402c0e080c40c601609000c070446c3c2251441c0240151b1a0b00003c840c0391000c01a60300036050040c401203031402c4031042001a18684039559442c0765101a10b00c0240c0003607412a207000c2c4040d140669901451040909450000b006540f000d020140c51100054030012524901024404400001e00c003e010903c0c5240c4880c8442d0030030f00c40803030310700c03a031403007c0e13004000d01d00d01140d9686240d070381e07603185102c2c054241c3c1c00030754090521170120400c0d05001020480c18031891400100103074481d40d400003108010307009003001e40140001402030030000d100d540c81c03140c4242030544802800c104036002 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 753538516 1250 753537266 753537269
    0x81005310c0e1c0309260618010b01020f030d090809040204152709020a030f150f0e04080d0b01110304120b0a020304020d02060c120c010b0a0f03030206060d032a0303150b04 76
    0x2c003d00c100d00314011404003050001940030006c04e540e103904007503c10710419a845200c008484d40b03001d0b078408166000040704104c802440e4050360510319100c541100400c00d6007015280e00c0303010080c264075a40c0b00e100500217090081500c0407032a80c09440201400c110480c802c000e20300d450360200d20b01e0941e00d81c950895190dc50b0140c2d1fa102039001c21809032a682c03400c50407003810a18a9203401ca0b0404416040e560307441d10200c10303250b0301c00c1840820441941c019118200c2008400c0003108181c008c0449a00103050450303410381d000305007628550083e03000058403400b504080c020841d80041d0340e900066441419419400c02d60001042640c03a0b040007032080c000010b003441d102c0000d0205411070980c2d0039460341c445115482c0c1a02034100701c138085114092052010a075607030404561810340781c140d07000f84890f6450006001750091520343c19001d2081004405008545910500d4001103580c0300d040c40132942ca242c040c5c25241034080502e46150b00b4041889000c8001042c3c80 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 753539766 1250 753538516 753538529
    0xb090f031e0c03070f060b040204060503150a03140601030b01060521040c210213020a051b0c120f010b010f020d2303010303020607081005310c0e1c0309 67
    0xd940c001c81c00201c000910402c0340901090001040410130300c2030200500306003034001c070001d00c070008030b0b281000101d200314000d03100459400d0011a80360321600e00340b1140caa6028103465151a02c0e43c454808aa03044480c0c504075038000001402040561f045050043c1035505000303041001e05640f00c0d0407484908003c2c4258440c00b0001070038032000c84140b074020081410b004071078000c1680710b600418076010050307000d610300c800500b04c00300302482140d000042680e07440e4108001407001c690205810301200c000c0744070f001071010131075551700010322070940032000801950000307200542c03c0d6100005a203040c44000301c8100030050f004030f0941104102d03480c00c018110074040390000e071828510341c27080c044000400040101900090741034040c8030b183d200c010043e501d40c0407942c066040382c0502c5030055032000d10886441003441c034800e105411161202c043d022021407403000ca40300d052030700001a0b14101c40d280d59003420310303c0300784601c4400040c8180d50520b03103018110400610400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 753541016 1250 753539766 753539797
    0xc0305161a03070809151609080a03081603090b07030617070b0406050a05040b1308071403101a040e0c1008150111100e010903110d020d12090b0c03040b090f03 70
    0x40c09020301884a000080805020400c3c6810100d1030001000c04503451f80303012a420103804900b80900061501c0741c1030b85640d403d41640d40d01010103848107081c191300700506449007a40710005a0301854184a01c41c00e903000650646081e200d459004d030341107025411500b102c00140a540d61100440782503842078102580e03510000442180c59114035070001e1451180441d11150203d41c2000650495450100f102c0d034103515158110420001002c8851345035010741030303410000f1034a422041d8115000c4c0c100080e0806c0302c0340401d05544c403443c440c0c1c51a8104404a040302c2c54001d881e90444182032802909503d800704198440c0002c074504181804550701802c494030204100e0307440c4a480b451001e01602003401c85e11030281c0344401c421404141100c01d1150042c3c4006034010b5009440c0d4001e02c04102c0782442511050102850b480001c4c2c0c40d1403801000c50100c100550291440c100500e03968601800d01d180c1001002d001c80386160807681c0715034409000041a0b40041b41c41a035074 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 753542266 1250 753541016 753541021
    0x11106072328140f120f0c0d11040509130b0a090b0a0504110a0b13170c0f06041d06030f07060801060503130b0916050406051810030c0305161a030708 66
    0xd8036580c1c42c6210340c1e5103841e00051307000c00c214041e10160444a980500c24661521400460680c24000b00c03540228070030203009541121920f078000032440f2400302d107440e2420f600c42d000300b010400c046030307007034058105031428074204842450207070350204c48403800700101c07459a5206610580c014048030100360701c0b1000701c0d00740549200a00e140d134000a01c000e0050b0352310f40070092a50021030560100395015100012080d419107420450164514090541d9440d058100a01e01d14094070040c0c00040901c07010841c41e1204183c1c40c1002e501c1c2051031114500441003620344040b4a6006040c0d822200c000c021940d040310401d8103489840c10441d8403a03642402e443c84844281d200070780f50400d84010302031002e8010421503007070600c0c840d00443c166159024481540c4d118841c403500303d00604248114808988400da8110b0400f01e910104640e41c0d44030090300341072580050340ca64104014500c0c03014030b002d28920007009071080c2900751509000d00d138421404000c0c418014000e80000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 753543516 1250 753542266 753542347
    0x303060d1103010e0d020d0f020601030f060e0a02030f03090f0f1518060d050402010210150510050c0d090f080f1515100207080f06010e070c020111060723 68
    0xc54114005400304891242c4001c2c05d0095640003c00c2005020652641c10403003c2d80c804501d0906903a001a0003048803a402e0f6036410040100c1c0c403101c1054040c6030440001030b5410b21911000010500c004c40e12403c158042001000384c0c0d07101c03a072252071007100440594a8843d5600e01000402c50100d441d03005d0203a41003003904000d8440381e801900040c1300d000010150f40321a0103503000380e0031141c0520541c00300c4411130301030281c940c0c04480136181c104114a40248070710404102440d166041414820b40705c1c2c031300f0440302424001700c0e0340c0c00014800440d039654140c0003002104002d250011047c07407095101c482e240e100680d444120400103091000e008044aa40c01c0050181d10718810420402511405a800740c540d44d406a400711514120000500d035040e40d043d660b201e8495152000241e4001e599540100d0500074036800820310560f007486660322402c0d2945401155807140791000c07511030000c2d50400c09084040c4024007402e450180c402d50418070100c11402d01c5481d000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 753544766 1250 753543516 753543521
    0x30b0603030d0e0303100801020711120c030a080307140f030c0a1103192616031d0703020f060403031b051e0a0c06020f030703050a0509040204080d0e030303060d110301 74
    0x10380200019080ca00c0c450f8006200000443c0b1505661207440102c54071001000e00340d10840101500c408d09622410035030f4034001c2d01d07510403103410604550740710482e84042410401075a01c2030342d111501004004106400155051007074810b021640c1c0340141800840c0c0141c0000382074036079140c10100d000a0114090029290201c10000c03c0320b88481c1d80008200300c4c42000b1640780009614614003500d040383c0c0200110840c00081051441c3c0c2c3e50f00400307480c02d00100c0b2007d0040544540866003981c2d51490313942d030040076200140071345a085005111040703500b22003640c002e4000b0801040400c1c0d0040c812030025200d20000518803619080492401394500c03d0350b01c412290f2305460701b00050000b41c880744c0d28495074180c6001541c446043c1e03203582c048030742a00942c204101c418002441100200f050302c000307041c61170a010710040810b04a80003a00040d581d41c0c011115a05007035000240078000580407001145103241640224040d07100e80440203024920204680c401c1c1e540a4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 753546016 1250 753544766 753544777
    0xc200a0f15110f070302070e0606090105070219120302250504020304050f01060b071709030607112d2a011809020313020901060e010215130215040906050105040f030b060303 76
    0x1180440d1500100c200f0407040b544980000c40240c42090800a8448603c049280c41003034028000b40c01c10200800554499003c08400c82c3c0c402c0142caa0b05480d2904800c01c000908049030200c800e4407010325010b0302d080c0c65212203a100303c4590f81010741c074010324079180060320000e880c05603c0c2d8585103405458080d046200038480e5080000114040d1080b502512000e230089010358402c031100210b000e1070388652611150180c100e00002145c05010b140f04200702c0d1407000880301c1c0c0030a6130000110906000c24000810280070901083c1c09204100c064084285608546107890148840c1e9502a19905e080b60602000e02e00040c00c0103c448488801041500415913503441d1a42a50300c0071780008400b00c4c800c4000c80c0000c29024403503a80c8500110040e0001d05821043d0f0140084c0a2402424034014201e4880c880b80140c40f5090040120308001007007036101c81c00c1c200480140c2d0116000241001020304c0100102d2901011900403290032140c5160542c451801180c03c1d8801c9 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 753547266 1250 753546016 753546041
    0x2d060b0d05070b22080a030f09080111090f06090315060102030d05100501230301140423060a080a05060c0a03060503120a0e22050c0d0c200a0f15 64
    0x29800c0008103001d02d500201144c902c0380100b14014049207104102110761402131003007a134890000d10001030300a0907420b031509518200900405e40d10b04010b030954103020703402491024040343e60041c6d400c10354142030101c4011030386507060a003008046543c500f18201c0d1480740301350402c013154159009000715055511900701c00d00a40c40c248005101c0c40b40c0314400d1500144d04105000c42c045000e40b04a8088400348545c02d2850740307800600d040110710020001c0e4081e0340c0d6050510145828602480e180c1c0010b401c0110b03174038101e002c02500242030744c0005103503081291810b0000303002054081c0c0c8003244401140d02c031080417104030002d001da41c009a4051080c41410802c4082c500c0207000d2420550742c0e12290f1b00c0c2010f05000403109600101407404510200d001607040c01070704070680c4110316800c181c0c00e1541d4280e07103009507851000c0c0d0030081380400140310044500602c40094098510307009202101d80303903858110440c086900039100000220f0510441d10942d0030082c1181071 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 753548516 1250 753547266 753547273
    0x504031e02060f0106090f0b09033309060108031c09170c10060b0711010e030601180b090c1b1504150f05011401030b01030b090c03042d060b0d05 64
    0x1000c40196481d04180c615001c407221041c00082c003248103566a03070030b441c1c030007150b04103041c0ba14101c09202e8009444040d407600130b599084d410389050b5064030030504842c175450380110103a110004101c8802030b04140e2540c004c00014442030000104940c0d00c2c00402c03040400080d801c070550b000074801980010060394482c0c603401c100003d25800303401e5020041041d03d06c80e040498030b0500300c40d0680325052402d0f03018480340000c95200450b40090303020606003810414070100010b8103050098003c2100c481603140d24008203800b40c407554805040649161002c0d003001c440d20145402100d0300c14050560010091105034801c0c00702d0140410105903007140e0741824a480340005465090403114036181488800c00ca41d09030150604841903c84001c003031841200044010b4140080030605254441c0d089400382d484003444588155016000c40d5107070f05182c548600414510070844200040e124032000c2c0001c0a01c44001000da03215400003080490780f800301d07459400c9a0f2007c5c0c110300 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 753549766 1250 753548516 753548567
    0x1090b0a110a0c031b03030e011202130e010602010f02070b1b13060503330108070207180c1e080105190b03160f05070b01090c11030d0c0e0a0315050403 67
    0x1540903c81c401d03680700380e2002c07141103400c4600650b03101c1d0b075100290006550300705409195014685201483d902e401d809072410070049000d07909000c1c0c95208001d10f2015000401a10340e080c0300322148080b250000754604036442e1907a05840002404804150740c075243c2c1d814404020408803511540d480114642040d50303000080d0281d00212002030002e941a041700b8146d4868012200054550203c4080040e404400443d0442c000a22042c1580310341d24001c40c40a0642e01c0c101703c1e1401200e0b0100d280042203100818001d035007000075010300e1450b44681c4403a904440d4090541d442078070f04441840080046c01c440c1150b50380300b180805070000501403400b081d52009404060a910380443c0111010300880b00c0d0700c698440640028206001408550400d8008109285461400225401c0f0f440201e90a5602c01650130a0069899180c200e0054110150341c40c05101140d80c42840303850b5441d10b80d0480089180090321a82d500b002504150107040c02400c01108000b5070200c0c3d4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 753551016 1250 753549766 753549773
    0x9050a050102030f0f06090411041508061602030405010203030109110403060906140105030c130e0f07061107050105041a070302250603110f0405120c031006180b01090b0a110a 77
    0xf903001351502880004c040b000545054051641035000702000341a0050a5071a43c40345503140b40f4800e031040e8480e4407440c45060b540d034090f54480190483c5406801c142c200700306006100b06c0030095103420754006100400ca0380e0303004000c0e00e04444020380080b0f401c003111406030045218a8000070001032074050700c0c0c420f0081550003401c400741422044102a41c8507004c0540d01c140000c1003942c01402c2d861000f020b00c103160804070240010b2003c42d403a40091107225030408110350031440000300b46e201611407105041144000501c000c1c00c0c024a003600b0302250710468030349070030150062000041c1c3c0c2000c01d8400c000100311035a100088805010600d0f94060324001c540c032580d80000c0c203010300070381d03c4162030701100d400e2000250003500c4c040c548010700c00f0020780204112490301a1051041043d01c0078003118111003190000012546c0c1400a1040007501c10300700800800d1500711440603036604588034101b91b0b4120301e8135a480707191110080710424010f140c20340c0d050003039902c4401017 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 753552266 1250 753551016 753551021
    0x601060f0e010c05190c0f0303020c0a120809010503070e041a0a0e0c0702210604051e0f0709050a06080f03041419091a06030907060e0a0803190309050a0501 69
    0x16840c8556070110000c00c0c560044850800c0c00c9000b4180d500404035068600003403d0b0700d1500b0620511035040302c01d075601a40e22140f64103038020b40140c3c102d00c1d0781c1401da00d030010401e0050309010001c49903059054890900314000c440c111418000c0000100702d0721406182301c0d0102440042062065514070b0801e011141070261800e8001c0b40403030004200c600011102a228030700e041c803d541450040e408002a08031810342640d01c0314440031007619551420f010980c0700b0340c0510002c19a4140410030002c00d00a00078038006203401800407482d40100210300d001c00c54614031700210b826111004000014042a408101c80780f140000c070780c3c0720a102201a00407100c441e8154100c01c03241c401805034811403055040760f895549981403106407501ea0000d141d10801920860b080205030300481c0c52a4070036648003820ba841134004111250740101561440354007603406640303d0b481c2450123540c1e03009a018107604482c0c41d000032000303d8441d40c00030b1103140d00581110101d20803414160300 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 753553516 1250 753552266 753552287
    0x1230c180f0d0c0e0a1e0b1c061a010e0f100e1809100501060f0302130b0c01141f030212030d050403080703150f030813030c060e190e0106051b060106 66
    0x380114000000e8983d8510340702d00a1b00446c1a854005c000149603404c0b030040140610300c60b406120002c1076012603091064072483e5a1243e400010b5010882e45070099001c00600011f0400822255403003464807103040542144006458036a415002c1107819114088842541034124005021610078001102d0045000f04c06840c20f5030440c036442c3c404071003640c00c01d008083c007007410b840c85d1a03802e51181c1d000300341d0350446070030b0034040232380b82c445490b059030050b54a14142d0713451300c00a4140e4404800b50681100941c4586040e02c0445090342107140c1d190310020340300320042002e0301c2c000b00052045421615003040100700714540391901605006041c0c8507980001d16280c070941e8520b01d042c66480588040302c00c80b541e0545560b40d007154030342c402c1c00204400f4000d0301001002400041400c030251005440e500c40300d0301040d060003040036003415440c00044d401181000344940ea00401419518203241907640c0d0720000740ba40061088010b200303681e1b0302c01c820000601550015070f009 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 753554766 1250 753553516 753553529
    0x603090f14150f0126010b03120a18030312020903010e03160b010f031a070e030d030507030f0b0904030c05030c0f0703152a17010801230c180f0d0c 65
    0x185512480070081409000b4020360651003072110005181541e003005e01c0c004a24050004654100d041c0c0c040b82c1001000b545400d1008d502151442c4402c2c1c004234000400d440243c182003400340345490040071002c00210081805500043d501440c1c0c50a401c0805185254822690703240b450281620300d05002034801d848100c1103400104048244400d61411250000704580703c3c40d2110f401c0500c480009010101070001c03074070350480c480d1030a01c1444084001901c0c0052076180090000d000d40700c600004c1e654203840e1914a03040766480010326034209130580b60103a20404186001c0b407551044099660382c521640f00341300c0c19000006942e800344c81c4a070b0400800c4000c1004500252903407040149400c40c1042815906502075181c1c103100148a0315003004040407400da800380d2020207800200e0240d44074101601031540e090850f00e20103c81018080451400c4101e0711018080e541c0c4140000311802a03101e4a50303143c4581c0b0800d044020502182200517141c1408460362601c60384 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 753556016 1250 753554766 753554803
    0x190905010807081b0d0b04030207080d0219120e09151011060f0408040b0406021c0215040b07030f02030109020c1501140d06061707030c0906030305040603090f14 71
    0x70070159408a00602141e2a03100280b45080c0721404400c0b40b8043d0005064000c2420100c03034011034a90208103008601039005801400d0130301250741d0401505207699410340d400030390100c0703c0c01c41c1420b03011815030300420050301c00300409400f180d01280001301300303610140c0c28051040c014441640c41030004170464107149001e1868009507004a4101c0724a4299002a000510a40c8000c84a10b80c4a1711450b00146000d44540142000d0f80142d049840180d00000b0000581f0024104501c50200c03240003d01e488526401d0170315469030020801031241200d8404106014040e400000b000c02e0500c1055440c1e60710b03014464000e400c1442c031a45603200d00c40140b4620014166024181c3d02d21a19403441804410140103204032500300c1194001e988ae03000251014404140741042c0180c2e402802d280c2340385040c200200d08d002e400c900c0c040d6250490400000750032100f00c07800c0b5015810f000c5207520710b40c100070242c0889030b07902a14001c00c03070000064020001c1740701404441c090089 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 753557266 1250 753556016 753556019
    0xf1209160614090f0109080303070e090c19140409060603090303050708040b28060f1a032502030702120102040617040c0b03092a130b010e13090219090501 68
    0x1c0300e002c480d209801050010400115099007882c2121381401c00c0181032451802d5078030060f0714035603481165000c001401c0080c03040154609083d034140c00c03002410003070703003004401c03070408401480da640d030030040c48400b040700000c9640203000d072801000028410800e036503a908014020386102c000460010745040c0005e82e481c0d00818405008a0f04003204064a0f51411019900e41012585030341020000f0040903001c00014002c1d280904140d00b018a0f14070302d40380c1c00c0700c1a0a013041110b800950180f0801008005182c502d4ac4611403524170030030003250314042a4118401c040020390402c84040da0083c841105400810841c0c3c00ba1350b5030040c02414540d0302e49881d0040d41d00030200311011008000502c1c4001c041c40d040b00200e802c1e9480031140c60002240c11081c0d4009040d0781d2034002002e400b0345801c2c000004460788211042c4616460b410008299000d107004492040505840c6006c041449600200800790701400c0240302258072050103050507000c0c03041403816402c0c0cc00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 753558516 1250 753557266 753557279
    0x4030c15050c120c030403020616020f1c1722170f10090201091e081c02150403030e0f0609070f0819061107120f02070503030a050f120916 61
    0x8403010008110b01510706032100140e01070300c41d0f00112050500d84414800400035946510081c0201c01030b481d01c3d0403190900d4414842c1001c54459900d12611700c030300000090ba80071a00b015256036000c1c0c00300304452400c002595a038080c0d11040d100b03c00a401d0200c007000c400d418268161071750303050540c000801007000d141e603500c00605454801d41040416282c0d0224541012040d60b00c141004020191160020800c9410414180c2c104200038001000343c801c042c002c007200c940038012035525800d0341c0800a50380e8088180604a202ca02000003010b161003903102c01c580402110542e445280071000c01359880c60141c6800a260080050018554040c10648022901c0c4980a80400c02c085100c5c8150701d5100a03041d1810b40e222190907681501a90040006520510555000200c610401440344540c00512401d5500c4050f0500042e90000140c0300c000d00c0038a002503445c0c804000003080350003035207140c1b005205a030b010b018200d040407501c1c00d41490400c4d04420301a030f0303600 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 753559766 1250 753558516 753558527
    0x12041415011a03060f040e060411042c010f0f0e0613050d180b030a0207112407150e0601050310020f0405120114011e05010918091704030c15 62
    0x100d20b10320940300b180300300096030300c8601440d4050001040100400c4031280400c064400c4900c8401058100340d00300300422098180060400c02d0540381000003802c0c000e18a00402c3c81d20061002c0c1600c00c0b00d905090b00000d4200003d140513122003440395100d007500200c0541504503170800e80740561300c0003403070642d807850b1000c00d2160013a0040c54410100b450036118207586a80e00d6044138920a4080380e40390060340158010b02d0351050042c2d03640f185051510302590b0440c0c1c00792240781413410380c5c040000d054a168488820000f003031039440400e031802e0562381c5030744d00319170954500300107103008400b0300800c0c1705040f1072058080d80e0b4403500110b281e40803845041906050424180401c1c42030b4100802c00b820107001c1107000042c0400500c5ca1212108000da108040040e18540740d03010380700750780058000a1100307081100305103091100d000303290650440714944041d9514100000d020050843c0359000120883c007c0d0744a880f07080482140845005540c4108500054000b1052007107 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 753561016 1250 753559766 753559769
    0x170d0302091008041e1b0b070309030209150d150509070f1a0c0f01061e1208090d151505180a0905011b0e04060b070305040b0f1204141501 61
    0x18407506001d10b01a00545021a0103030054503030496090b4110300c0c1560080040c400f060003120b00f107011a03000d200458002c40c01e81c10000340860107001a9000070341100d041c0f81500d81c1203a07111010344e503642c0560218000991a50b5009140c02421028004c507913003032000d209c030300600c00c1c40a60359030110356a55440b54400d1100b2420f289000300084002c80855405c1d03000e8088406250500720040342d85003504440e208503459545210070440c0d03010080c81134408007003080c410a4000d24200180f43c9111103081c028044900024450034a90b641505000c0c81c141d10000011a01200910000c01026040e18515521005000124140c075100c094040d0f0400e4408590509a46881c40340003c4c11050b1003c840c2c039902c5d240030b410b049001e41407a505903085a5600128112440b00b00030555460b03038441c11043c0e80400030000441da000302140c080d1080c100e111540d403420b01403c08158410b401207244445050803d01082202c60015204458040002c40d1940c1c258003401202000c0c1c20b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 753562266 1250 753561016 753561019
    0x30b03030409050c070209010806250e01031d0a03050703090503011e180b010b122202010c030504031547040b1512070305060a09020702040b0a170d030209 68
    0x50004001d0b40364550803856010200203d014280740b00d41e80451001d40c0207070440300858109008004240c0103200483e4680b42074411640c410302c40a200c0508180c440c1e100d0941003588070341880100018202c020a59001143e003110903405207420300030f0543d006003d045001902810300004c0500d0140500312a01840070a2018480f56107c0c14100a00899449120324440910b0660100b40c407600300d54000c020003030a6a56030300030300390904c00201c8000c121000744660f03109202818600042214102642820252030750200c81c05d068404e4001d45d40010001e51140c140c908141d001e5801664843e02105c4c0c0c049c01c0c460021003503480089850511290428250030210800700c1d5200725801d81c2030000e800040c03101000008502300c1c00e68101800040070002a0112000c01c4203001194045d100b4907082210342000301c00115524098450400c1d000e4021070345070309540e42c650003072442d008010b00c00e80c100c99445424218061180030b0090150041400d8800301300c2c0039000300c83c0003800 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 753563516 1250 753562266 753562273
    0x120703060b360619080105070f0c0b0402010e19080d030c11060705160819090e04120818160503240112030908030d06091a03060f18010606050306040c030b03 69
    0x100e540ea15580b90741e0062a82e44e200c911082541e440007580c404c02d8001d0503104001042514100c00058580742d0340c110312108210340b212640700480d9101c40444e41103642440c00010707610150000480050748100001305508203031a0014002400044040103548583c4007401400a405820303592407041782c00034040c40c0c0080d40003916003403007200200910070707410040e001404c08a89440c1d240e034100c80e100740201c0100c034212072809a00700701104020100020084614030f00317551014002965508114180819400846c2200702c011440c418540046011035030034800104000728100b8407441418040d000c3c070400500c11418500e040420034041c03007802841a4130780304054000c03003650b00d4260104451030344081220340f810700c014800510000d10200740c05003400020011907105104014912081441c01a0642c4006c1049070348580b03032140300000c0380d03924027000d410b603205a503030400c4551818030b0200705950481c014600407241a2410028071608007400d508031468940095419170 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 753564766 1250 753563516 753563599
    0x307110f060c0d3e0f0a050102120906011d0a090b07020c01030501061407030c08090301140103210e121609020408060906040f1e0f0f3e120703060b 65
    0x11442c1050003c4c4110610490351107002c078044050078020940d00441c2d81b65000600c00f210703980840d103002e0300040910087c00d410351400c9114000c007001c640d0702041080c0ca0400150000300720354002c070542a04105820403514052800940301c6c0529552180868a0701002041940c810750340941010400c8546518064440d2002c3d01c1c2c5d04a41d600840d02c40ca8100800311403a02d080c020b1002c2e0449245210b102035056181404040f1016800c00d140702032108903103845036500080b6803101001c2030758082110060f410b251800c1100f200c001444814110b6000900040e041c2d0051007141d81c1c407400e85410341c443c404155210182510042d014011044a0030040740300c09030440940c4901012803942c2c09540d5072642240340c0d118405544890070340490100303001c00f402c070045006a007018184208151001d04065112004821400c07444521700001c2d1540ca41940301e4400400c940708881646649151490141540041c0e030380c0a41c416070319506c500008000102c003402c01880c500c15800 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 753566016 1250 753564766 753564857
    0x71e0f1101094d01020f0a0c0e0c120117070801060b03012711040e06101e0e181b0f1c09150e0705060c0307110f060c0d 53
    0x120300c29506010712020b00f02100721691244010201c100200160f8040741600c104006424a4910b85240c1c1d150b41100a2010002d260a4030038420b07101c409240c0b490b00c1d210490003009501401da0484a020f031040000320340c5482444181c510884840121340c4000c2e101d400c3c007420380c0e04a114081c0f03807034424001800459003200c00b0030315803440d0301646103500b22408420700075101103250300107041800060601406070303542e5000d0342c400e0054511014200300d0140c01001e145100d806841c031214400815071002d4402d400202da503107002420400d503110004d1a2085014050798200c170886e1215268500031079815045e01ca40d038400740720441c18940e030002885010081c5080c010341160381c52401e5000244e0720034002c842c0316815000016520080c26069141c0300217074102c0d6100e05001d1000d00d800003000011559907651010800380c0c0400f00101041440d83d581c01496804040072440800314480000c500c1282036195842d021000d09198007000210409a08011041440306549410 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 753567266 1250 753566016 753566063
    0xc0b040501050f0702030c1e1014071b05130e15040206120405120301031214041422020403052404030804030c2a1a0c03030708071e0f110109 62
    0xf400641515447c51810b00050a40540105101c603940c90300e103003400140c18802101c040d2501e181c180844000d1060030123400f40c4c012200002c01a00306404004541140c1c49109801084040c004000e900d209618600280581c0e54a95215200700c0b40204054103c414501d405181c01034001454040891080445040001e0040d1224404c668070b21805180300001075000b58010b403645503440070340702d2005060f451809107400c0b03184030170701c000d2014200d02645103112550031201c09070003800d20442200c0c500c1a500d000000e130741c400b00e070001c1400300208146d00d410070b111094022094071040144800442920054000f80300c2000060010340a003d0401006000da10b01002c10320040d400200070030700c80b1100c0c21b184031804c2c1c2d0820100c040c0f0b17801d12100e1100d69045500380024501e18030f940e400005c0100003006560342c04605068000d41500210005003000c15048000110000c0e103c02c1141d00d0301400201c3d491100040800b061140941c155400908a640302480540341c050 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 753568516 1250 753567266 753567277
    0x11e020106140415210f03050a12060b0a03020d0f060909030f0f0507080309010219030605030708151614040e060f0d0f0605060411040906030b070c03170406090803130c0b040501050f 80
    0xf40404810045d40414410142c07024440d2007552116078072514000d00420900c020820011080e04024051100d44108410380d122001c0c18a8016103440c80724403401e002c0c0581214030340b0103924044003c10340349500d4004500050080c0c4580f50300314417144e0704a41d80c42c2c000c40000d0004000380b01280020784040001c60700405410009418141c1408198114150b94070280c808030396101e03c200f065003401d03c0780c48020003422001d080601c0141a031382100030070043c403000c1308030302050404003142e0080070384c0040030360b81c0804640c6540c1c0b40d2030005080d84040d14480c4c0b14202c03d1062000c68130b81000d680500ba0350001403001c551540e941c60030050302c0068038072507120780c6030744070103541b28241005007004000303d080200344245142032401110201411038020070a52001007400310360001e54142c0c59442110390840d940c0da0304d003032000061008450003030007040c00200f440340d482411008402528090b201c007101081e036810900c0c21505c5684541c6010a40600000303942c00000d0001c7c24 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 753569766 1250 753568516 753568559
    0x203160c320415081e0607140702060c0106121406241302090d0f1101030c08070810050d050c0a0f060f03050c040e0405150a0b09060f011e020106140415 67
    0x1c100d51301d6400302030800c00c054501c0481190702840b400b5a00f48104041c5400502508101e1000c4510010f61403151288000203805520300051070b00082001354066001445000304064a00b002c500d8000000180c0c0c1d50f841d4201d104200101701d001001e903441c0f0070945146141c0c050074034581d80921078914442c0801c280256424441c072200c680302d900c1a807042074410420002094580e14000881503001e50360b1a041500d41402c1c0003245030401c2c001da8010409092124060b80c1d01d10f080914441c03260095604000b411400000704040010071600624003182c2200e5000d441d2081c2e40c03420610351165200080214000d034034401c2c06544999000030004298a01d07141d110300c0680090202524222052380c020381e80c6100c0414032484640d000321041c07800b4081807414a000078a0454040e0625218010800c800c4a283c1e00031114003041c008030340310503da00015140e01070f008050314441c0c4043c5200310014281145024424840c075400c0b2401d41100c1c0505101020448015840001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 753571016 1250 753569766 753569801
    0x1003121403070c0303050a0603020604051309050a0818010804030504151101090503031b07050604030e0607060f06051009031502030603030d1a0a120201021c0203160c3204 75
    0xd8a21180340118450900d80d256a5000c000520f8010300f00e031b0f00148403e003024034046091006a544a04079001c6030b1044640054482002e420080101107030000105103106032611082003001f05c8010705000d0110200300b00c140b2084200558041134211002400607104100c1400144014040c8600320011840c00544c3d0040c400c942a084542c03010003507415138408010802000c003458042020344e801d959031203080c4101c541d1455551040588003c007480304200c4504196124031095902c59508072034148510085025510000c144901560340104440d0b082618181d002d01c0050045a82c41040c0d4402800c68180d21402500094450380d07141c0010086200040d0300c40c0201300c5240d0346481000903c03d03a810400860500c00e600400540c0d141456090240c1e0300407e0004003001c046000c541601c2806c10100d046108100c070801c5200d103690117810030f0003c40f40401044d42c800c2c868079640ca9202d10b020a980c2c10785d0041c2182d00c4550b02013620098103064104104050211008 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 753572266 1250 753571016 753571037
    0x70e10030c0228060e070b16022205071416021e0307030302150109061203120b1012140f010605070203030403060203070c031e0504090b12030408060901060509100312 73
    0x229255000c10158109524010070f00c403000d1003060310612006010120080031704901c0c081c12003003076000e182100d518040010192000b9515008071a13442e41c0f003945490502001c082d000080100025200a000203a91401804145820380202c44070a40041030001d01115903500704601e506102555104e20b406640c0301c04840e840420040014600c2500581814213401180407842c040582c00341e4a500c1c1088000c0182401204038201043d0700351410b81c03401001014400082c02080601d02e0300044000c098904290380142d943d41460405070080c000900440b0404500b0441038404807440e0304d16000400056001e1401480485c0c03000d01943e05240e038a46810b0200d030800c40f0403002103140c88003d0010141d009411a043c98644551071050188080000304140224040c8921059590400c80000e40e2544c1c01d148801300a08210395a45448102c25034a4a0003540c0d200c02940c00d0481c041800d1401c060328070721620b41d1901241409245441d90031503112600c1c551414807005204 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 753573516 1250 753572266 753572293
    0x181b012001090605250f05030a020a020106050a080c010305100e0723180924061c0207030302071403250f020a0608010f09020c03031f0e0a14070e10030c02 68
    0x5920311607410a00c0302400c4042d01e0075464007402c451640da40c104500c8100d070b031b407a8540220590380c22a420520058613504200301c00d030b0040c105a0480307a4405101d500000c4c40020026a03c5041e03002030742d082c42203031075403608036000420030700402d014003450000007201c546c49505008200c0c03001500c10100c405000c1102007803540300a01f04108004039200c80d125609000c0c44227908018402da0106100178540b141c800d807005010301240c865003000901d030000c80503240342c40d0300b45880c41c2e03400c40d540c503140d160140080d030102d08101e4007198502e48004a00c600402524601034400304415905000503108000344c060340ca608451009443d0313101d0380580c503002e4259015180742d403242c07000c03541003400004290b002036019081c1d40b40104110070221001100b5a0b80100b5240091420403c0e0300c500d00d071080071190444a40344d070040d0304100004445030800310b06c5151601e64444252030b421004c46000c0c1011190b0341c1c00c688800701c3e1107038282c440c2d400408509018070590345000c469031b1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 753574766 1250 753573516 753573521
    0xb0a0b120a030c0317040803042a0302091302120601060905060403200a090c0c0b0901090302070b030717090a020411070206030411040216030c0b010909020d120512181b0120010906 79
    0x1c2c6c041c2da040c4008010001001481b54944940113401c48040c100030b00500c00707500003c101408001e014916100c0801ca9094400721203625460f8010120041d850280020503502c40703091080e400082e0784484000b40d541040c40c01c88042d2500808070f0300e003040c0610002c403844464508015001185c42100184160306481401d1100301c05694186900c44181810001920041c0a15407207034909502000041c1c0c00048243c201c5042035000307510703903a410401b034405200d00d524043e0041010010004805030110750190302c10710840e420014a4103070100c043d041d01400c1c00080d007003201000460080741c4803030140070941f80c0003013001d46000c81c1054a01c0106d100f0400c200c0108029400c041c040009466078507015110100301003080c22103d80000344601c0359100060164945405c040b1003481c403881c100c685054110300bc1550740d040940009901d404610307070390704450041c41070310300c8503c0c0010000c140c3c0c04816590860799030784601c04c1500301d20041c0301c1e86031503640e40c03074481000903c0e50 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 753576016 1250 753574766 753574771
    0x60c0c0a0c18050c040803161407241e11010e0d02010f05180607050d20040329070e04021c0501030210050307020607050a02010e0a0b0a0b120a030c0317 67
    0x4103407800c00b8520340745584054490150180703c06102c288401d1000e40350000c01d9514403121100c3d103600f980c19600340010a04810200f034441401201d0300418400c0346030340c0012a1061149410a540341c000341c04465009031841c010b40c0c055400b40303588031100e200c5d204041c030141c0e0701d1000042421103000c2c510700c1d0108008005015075191b04a02c462100c462140320340c00b803200500f0b400c0805082c00d12540724600140040e051240100d410b81003a9905e86c41155007800030200400507509070101c14000742c01501c0125103e90144d5100c10b070704071ba5061105902c5000b544a4801034903000e0007070301d8020f14027a125402907402c0c0a950003980482c411303020004c03020080000c403541940140f000344581405c0d0078051003020410f01c410140d000070050b070701107801c2c500f86440700c40540049015000c40304a0705201d125058810050000c090380715400b454158808010b02c0b442c20080c0090203003004081c0607590045000725003c280079808400d00315102e4035210b10031401680691168134020f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 753577266 1250 753576016 753576029
    0x2060a0e19060b01090503190305030c0d060608041104090b040b09210c1501060509131404060b090a06080a0b04080415030f060608012909031506030c0f0102060c0c0a0c 74
    0x3c6010507440c55800540315005004281d01510414071101c0c03241c0702071010034600900300480040011007a00b02c40082d580c0d0615101003d1002c1a036940000300502c20941c0c01341c0e4402d1050342150340c18030702841080180c1d030348891405144d5860741c07290840c1c103500901f000325900809088202046140e81c51900320340102c0180f58590508008903860b05101c18184813501403408014400c103a00030082c0c0e9580001102c80d54002c02e00c0c0200300028040e1000e0741031060b1030580502040000341d402c066070984095411f180d40340e56280381d101c2541c006115204071500040001c04c04544044c9805074001e014501451038259103000480403200501403031000699271303929031068240e990049000403c503502c3d116801c1c0d41440044c0f80010f2090b0315400e10b60100100d59008152580166002d40c1d00041c1a50807092540c0810404094219049407090191100b036100070b240500c0d08501c5c00906034004c3c0b41e0b560b500400c03c4d00582c443c2a0a100320700c0340e07200da2800107a5001d28103002d05032 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 753578516 1250 753577266 753577271
    0x4140d081f2303010b09040f020f030303270f06040c03051c1d0a051504090e01050f070f110d12140106052203061109120d02060a0e1906 60
    0x5001c580070701c0c8100429104005030844800400044898031a00b500a11454085000403007580b00044e004200d0004041c0d0061500e0040000380055414003901f414000e0311a640111071504c00c141e102c2c441100d800000128400300c000304281c011009105ca6615441200c1c1d41042c58090b203450540200c90446070b484060301c1c14820004107003d44601d0400d200c03001c580c081c1c040d4001405000754641c001e054800c40d0785500e44156a82c0d14244010f02c4058110302894840a5407e00b07a80d016000f0302d82d145042c40b1440c0303101001440f0340c0d84942c1c00d080080303040d47c5a010b01201c403148100b00d90020424928030315425214107115070f443c1003000d515143e203210f0502450a0076550715408a112070040d0306d0041024a401404851042030045030240840c040c0400010400d0181d0f0409010189410b110100101e000001012030400440340c0d02e03034418880b1580d581d1040340b901c0850060b00f040020031243c90031604481d06100700300c0c055562035000a80d50035040c6c80a43d00c2990450b4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 753579766 1250 753578516 753578521
    0x50613030c0c171501050f01120f0e250b041215060602010504031706130c02210403050f120d0c0e060d0f11041d0a15060e0a17060f04140d08 62
    0x3c80801c294001e1490114603901c040d80b511000034650135860440d0380c140126441c4141009140e41d0140c900111000070402042200803003140e07481060000d9841011024110140c2450b400c807112011a062480789a1501d418603803188181d481e445400c540d0100c21080040400369980141c0e03000d030100d940002414034141c00c00500030881034120844410103c01480b049803540c456408500600742c40204604d014024101c0c50180c840c4018090b50070300c0c0e00a841405602401007040320b00500c1203030103070344181b0302c01c0352070b0b54102414407880d040030421720f00f07181c40300d810003041d04039a0708002c0102240c40000c42d089900c6400240c45040c3d4031005070070070410ba446001c03015003424030510700b89030402020916114030141c0902c1c4440a40d000900d080c016030b04055161404032915031001540d80c0c02c0030301580c2c520001d0522694000c1004070300510110b4800d002d9009103402803c09880703902e01c0340343ea4900580107640c2d8210707101d40036510007420420f000c003071907503a03480d2070051 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 753581016 1250 753579766 753579809
    0x24090a02090109050d150b031c020307021206070c0303092d06060f050315220b01080d02010912181703070b060405130b10181b020703050613030c0c 65
    0x2c2942d6000140315070300340d0b1045e4010441c540701e0700e5a2500c515800140c20750303035440042d24042c9485010840080c47d02c41e00c070b80080c0c0c0400a4508144240c644141c0146404420b648843d0100c3d00000003d030304850810200380310b508403149444c003c6001300c1050711000d404031000901001000010443c25043c0000c104003880f40318001c00c030a82442c4010f909000000c0d03104d10b070186051441a40c00c0011480c440c880c49c80c00c0368911880e0005e02d00d044040c0c42c0a00100d08240f00d10703030300c602545a10300901401809100074855000d110b242000f0503100303095414070644510300007140b034a6000030400d8039111003140401c4002c40000c64031011240382c6503825201c0208618025410142448440150743e80c80308aa240e104103444040d5032038151203030000000c0d900400f01407441c040014103000702980310391801012107143c40301455002005a0751140c407444000c04070741c42180040c19500260305000c01c458072034a072120071980d01d1b8980c4520401c217030300203440d400d01966900004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 753582266 1250 753581016 753581027
    0x1504150807090e180d02060907090b150403030c020118060f03020d020d0501170c0d0f060c050f0f03060a0e040b0c0a030908040305010501151107090207021807030905120f0324090a020901 82
    0x710f0b461b4030003480207160031204240c6400d00c6208020030790340c440e4514588c5540301c84503055640514030034592602d5607810020f0541d05a90003e9010815107004c8509080b9100c0d0f4030800e0701c07507640b1080c1010001c0d002c214000d500003d16140308542c2404145016641070003958000e1501d9001d49410100200c852414412286092032003a448400e003440002d140b5882e8185098200d1000207504940050640d010b00c03488809041a0b80d000406542602200000d140508016541c04881c10b40340c4800c8241e03680e06480140007049803400080f4074010007802484140340714640400c01c003000b03645281e600d400503041100d00381d4441e4010300401400740c0d4000d040508500c2d160404030b0000d03c090303444542c50300500100703980024540042d515008030340c0f000c0740100c1149840901e0710303c40040c010080b5a004840030700600f4400300c44a132818003a03520b22243c4601191450f04c1d00070304c642801402c0100000c145e600d00003e010705d980c2d44403005110f10303070703540340075a4851701240010301c07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 753583516 1250 753582266 753582283
    0xd0e0633031c030c03020405031c05040f0e0405120703020307020f0103060506040b04090b06090604030318170a110402190c0f060e0d0e04090f02060a030b040204060302091504150807090e18 83
    0x40600c103107c10806036400241404c0070b246031305541c040396541003100300c6042c800ca0f004100b01d02c414240001d0740c080241b0001d032169001c0e20560b811061100d0001070140f0481c40050016481030210310b015103000602904600414100000c41030354640224040c1d810603801407030b80070780124003040811550300681255040407150189800e8000f0f000680034050b80c04054108000804a240c10b00c031080c885030050040560914491070403029035990303070780400b00b049905c840c2060380c0d174459051074003d0710094500e81404020741801071004444090700f4050a84083c1000010080821111f00c1000502c9225a016090742948010041e04507034650003400e00581c038003e01c685c00304120000c2c0101296046802655864002c40b08501414143c8000b80d885480000d0020300d854155000303000011058400364143c000440054800b40941c2c03040020602000c041080d43c180f00d80041740e801b00755401c001e07925a494518134881c40d081210364194140300c0c607140c1d40d49081308104010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 753584766 1250 753583516 753583541
    0x1020706050603070b0307120b0402030c0403140d0e04020a0c0b09030c15130b0a02130609151e08130804150801081c110c090406020d0e0633031c03 65
    0x20b555140905c100d0451000414410400201030410408400319820003155228020425520f0b42000c15940d5025441480111031020403c03141544000c0041800003014003980c84044150744a00e0510010350700c40007915080040300e54442001441800f43e0314000c4402c070009640f81e1454810940c502031020031510390740d02101e81003011388040705038003040351a407009510941e900c842020b00040c1c050030ba04520140358034100892001e5000000c10101d803120304132500100a02c10b415281000030300706c201c0f0302003c00f541440415026070080c51304480b00880c0801042000d448d11726480c2c001d90019980c0000d0030b44e5019081e640a05400c0c00b40c0f1214000d070602c22800342e0410701080c1518650700500030021180200314406101d41d00d810710016060000300e10b030500d8a003000394014811821102e2529501c14410312000036060300c07482016059400745c0c0700a1003c0c540240008601050000c40c0290746951070301d0070321510284a400d0811038046a40c07195000c1d0a50b2011751041c1c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 753586016 1250 753584766 753584773
    0x30a0f23040f021c1a0c070f02040207020f09040c030308010b18010c03021207050f0105070e0a14041b080405010b2403060a08030a0f020705240c0c04050901020706050603 75
    0x2044000611550001d90129102d400400a80701040031807040380e0b080070701d03819400b01070028024421000e02d5114150792204201d0364031075042c0ca509014094025158101c2081c03e040141010ba0042c04c80900080031440c3c546181d40009034500303030403581110a500d0010301001010b0b00300c407009014003220300303c5a0412000c10350810071980822501410031000500c514103041c002e00c01c040b0440240b24030203075501c0345402c00c166600051004c9030f43c10340c81c16001410883c81007449506d00d40006146108540c6002c2d06e404c40c1e030026100c542da025981d07541648001d18840d089220b03410080d140d8400301d240c1070074030794211843c0c00019402038a44208036501604000340c0b000c0c0841c8205030542e00c81d100d071000310b8a00e090343d40122086100000c1c51004440e0421410620654a0707402c54100315150002d02c4000c114042d036100c124000c0c40741101052940030060000200382c1001c4440f8054142c000ce415500c007900c03144200d0354000342d4402803080d00c0c09a9a440315054005 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 753587266 1250 753586016 753586061
    0xc0d0e0601061b030309050607231218011b090503010b0a03023102160c0f1a0a0e0a150e0a0509070e011b110a081912050d02030a0f 58
    0x3a00c00c80d000740c803c100720340400f662802014000d901040c10303160003c1c02c0b103141b8a0602d5001d080c458480750100c28401c2c5586c0307140b0303510712010215000304001d042c05e111a03449801c4d1900104200c103424020b15500e0360000004101d515452001422003a55550002c501c1d00c8c1c00d0500719400388448a008a040c02418000b40c0c403a80501460f0700407021007000c18000030703030390054440d1078144036803282030000454008590b0048002e0740b89034003440c80d00d250150f459403441e4800e4042c0c443c01100c51006020301060090703080141080e4001800c05411008840740001c4807072066400c00c42d52941001c10581c0901c0e80420f07140352441e400e0b40c206018030b0800c4009580350b00010401020031014144200c050303480745215040000e881040030748481681d2808840f0410100300d0b00b4000c0ca80c03545d0003d402c8000186102103daa00108202c1c140401c2e01e9180d00440d1492005060083c1084810a2114588001c52080114040002c0c400d02c43c0740c0139409542c0a080040740c00d41c0c000340c6 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 753588516 1250 753587266 753587279
    0x60b01050307350412140c0a0f020a0306020a0201050907080c0618010309080a030501080c0a03111908070618050a03020a210c0e161b030c110301050c0d0e0601 70
    0xc400710050f0798aa01c1424046a440b1004910000d280d070000e004004080c0020801582d500305580c5607145c40311740e00212042450b0f03015024002001006500c40788800340442e2071080f602030000c0c0040c1120b050f003500c903250072080e80e00800400c4d00503992401007040183c404d00c03280000d04404405401081c00704400149280690003c0c40c0c803041d022364103240c0580c0264403120345198001d90b03180e01ea103c0c801000c1c005000034801c40c00b0710f0140c425103000e035107440111401074a9002c4456011b0710381041c2884180ca00d41511450714105030300c008100000200000c2005105503503544440180707403503e01c1014a10f586c403041c011581d1b22424401030341c40d42131410aa624440704403c181441030b81d62214110950405410101250408144480151402c0744140501d5010340046144c80d0700c1103606050a201e50400f10100c0e000150000c1d108510f05031a83e8020642038800041101c00682194001e5402840b082c074001480381d141001070046080324400c2e200a088290b16000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 753589766 1250 753588516 753588527
    0xe030c070b160803060a120305040312030203100e0603012a02190c0b0708040302040603030c1103071511010204080607091a09010804020d0515041104060803070206070b04050a05030f0304060b01050307 88
    0x3503005106810100000f8410780711b480ca140c0c002c11200c0c0b240f00030300260b0b00700a810782c2d0180c0019122406d148400182040c0240201c034041c4040c00303407a5107058a405135034a420131001c0e100980c195210404507511345140702c0803c440c002400644c0e690701d0801c1c800070349404144000180d0401c4030340b00d80d0b4086051010803100715081c1c1403000d40c3e21841458085060310898000a610914220020042c1903010364007416551144000201a855138000c141d50740e070f818031845881c032582c01c065017034542c800d040015051503504c00140c105030704d5050701400e280040301e400000405203201003000b0b1081c024412440100da0620510701010030780001c3c000c0030000d101134055a69218180b04105040002400103d15080101200d043c17500d80f119403201000c06d51403040c4c1c10490041070400000c0300f01c80080343c0c01080c00c2c1c601b0034035a883c010b0202c401441030301c99001e4a1280004a6401e00040c501228030110f481da41b40b8007031401c80d00f20341c1c01c288140e040000610402102c00e4011 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 753591016 1250 753589766 753589807
    0x90609200304030e0102392d0a172103071b151b030606020c0d020d050c090f07180b2b0e010f050a050708041506090e030c070b 56
    0x1460075502c026610340c0107074504040614200c060740d9600d040c1c581d5020325441d12096003010700b40461100c07c070705020405450924511400204007880b0902060143c00d03202c0c030030501029050a860a0f030b50f07585800030043c0c4106425040c3c200c1c0c9940c13044800f550341c0210040742c82c40c26090071800c0c403207401840c00124401c0e02c040d00a84400b540148040d0f681da0007802c6005000c1400480600c54815002c3d0b103409511034086420150f001c0740c854004550300c000244050829684082c158081003107003130f98000706440a020b001403a06141e200c83d01c0e214813454414401118a04190000400c41103100d100c00c80302c03400040c824021f0303c0705041143e800701100c107586420100c0d2149841c998400c1948444000e038070f4121440c2d583c1c001900603a10400e0800380811841d41d491070920f0a0711412036040c40042c0c54600000c0c0001d00d004441032501c0000500029210740b0748101c401140d10082c4143e005910106002c41c010804200f041c0140c0514072900341803424440341e90840b00020f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 753592266 1250 753591016 753591023
    0x1b050901030906020408010e0f01111602061204030504330503041505090f0105090d0f050c070801050406050105030d0c120c02031c0c0c0f12030f0e0a090609200304 72
    0x4420046a1094120000ea660000d804642d01e03692403640a000740340038517884038503028242100c0302400040c4520003401031903031009460038082108802054070381e513504a901c170b6814007005088404202c81071380705900c0381d04c6065459042200c00c0c810300303401241908014000030445680c06030151803950004000c1d04040d41c0300e850b145011016000d402d00e41600561a1404010280d60006144880d5030000002040030707480d8059480e89407100e8070750720004286030700d00304003001c3d10130341c0208110341840c3d040d5440c06803075698540c2540c2e0192803d0396075984600061207145010f06c24640032225a0030300c002d60840703c0d690190501441e80070501440100341039101552018003d00641c40d03000b00c0f011a0038038400340080e018038050318003500e11228409001c24020710340d54001d002d4401051400041014603581117480740c00180f0443d080104480c000c40c025114128000003508410a000c6403450801c0e0036070044444d003503004908580c4266082012500b2041200c1c0c01c55003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 753593516 1250 753592266 753592277
    0x170907050a140d060905100e03040e011e090c030207020f011704060f151212170606030a02040b1801230702130e15010608060d120f020c06070303020304050c041b 71
    0x7814001014101e46903400744c0706900300b212160800901144c0e46000111f44101040241e43c1d100030a9034a0082e03020346401e121f000b1005201c0c00d90242c05c070324541110281d5001246440b00f19081c00d41c2c26201c000301c0841c0e00801c1e84403c5192242144210100c2841d20800ca0419840010a600c07030160024020503034540743c014600c1f1241e0004000b440310145140245a5584c1400c054003031102e600b52400074126070704014103841940095481c11510000407120703120700c01000f103d944060002510603508100006030019608040c0000b0007214000c20425040040094014030310200301020a801c0585c1c2031001e840f804094035419030b010ba0351074100241c9400c641c00100300c44d83d100b501030700c140194061a08528070704241607034074568990b80303d0b48603034041c800b030301d405c00c00003c02c620100710907441f8240c40750390004c1410703100c0e104503404440e0190111790243e121710801c2c2c0000b90008100020720008220034031030b100095404015801038900703407417114546038411104001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 753594766 1250 753593516 753593549
    0x619030b130207030825051206012d03050f100b07020604030c0b030103050f03040b0f280c110d080f0705030d06090209100e011e0c050706170907050a 66
    0x440c0c0300e4040040240d41c0074110350791403190802070482c0c1c400f03c502156641c50b01c55030351a02c3c18500c0210801c80c4e81512a6820a003250104251624004000b1070401c010f070b40c11910040303405014214510035091170710348138606400c4024140c800003424081880750000510105c00c400c0b0400b001100d100082417134075000c05100080d1a4443c940c8003420025500b03402051501e64000114102c9200f50226444900c000108503146e000d00e2152a400074018010b8a4010070007200030441d00d91420507203078603041d04414480001090301035140000742180000010080c0c80c03111004411011904d0f1206483d0700e54914003d480303007800e90104d407203002c40c0c00700c2000390810035511804200c4205204d900e03250100c8a0007500560905071040e207051401c101114043e1400c03800004041e03664030b00351b03860b822006100e01c40103000c0740e00f04192001450040780080c044000541025507034582c0020000c0016410745201411605030b541200d0000c008540d03c001181080741c2c82d01e034180c00600b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 753596016 1250 753594766 753594769
    0xb0c1210063f0f050a0b01121b0507020f130f14010f050622031101080a020702240403061509051f150519020c33030603010902030d1d0619030b 63
    0x780840440395200b58100024070664605e0b40e0000707191007600385d9820f10070385c20b800d4104058401c0c443e40d0106e8203141e8600302a10600c50340007044c4190024004880f02c42c0c096020408042910b806103014980c1d40440c3d810030441d90260040305101e40e1083c04855060601c014220030785480b0b024440c0c00d0000303600c8480d038000240881d000110030910481c00c0c1e500c0c200900501c2c0c440301c085000602003000140700c00064400d40d01030a401604221030802c8034110010b948000400700d1000c44000c2c400040040c0c414051a414100e00018114031185019014406c0d10000b90a625061446a1010100c00c0795600c0b20002c841c0c4100c42700c00030115440c8103491901c90000c0540302c1d500c1c03140100c0b02c400d0300024100b0100710103513000340309100e01074503035020310849035100482c5030407111900510000c042c005c0c50b0411001000050f14130145d0f40000c2c90203802140707000100b60b821008140a426541d0801201c2c0360945155103800601e00e90000c1422214a200c0203041d0368610102d1300c2e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 753597122 1106 753596016 753596021
    0xa1d0405012009040b01110a1a0105030303221a01060f0806060a0c060b0411131a030f0105040e0705090c120907030f0b0c1210063f 58
    0x100702e83c020401010b42905c16800e4100300c82402d50982e10750b024000780b24260b102e41041a8001001c840c500318112050380218030035002817080050b0102e100100000351011581c044030a149285040100c1100c11020201c10000c0d4200108016402402c80d9032850f9141d00c3d0800603584480c10000144918020340300083c442030300010000d851a040740400c104001e201150048010b03500c403280d50442514515101c24070700003040081c10007088981c440d200000814918900b00e4a103450044040c03254a001d2980c80384482c8003000140300e64409002d00810000c0d96041002c50b25101d40c200004056413403031843c004c00c01034200040c00c10116540b00b01a03030403110090b00c034444007607001061807403071510405c40c1c0c4807010010481c4904c948078141e2402015420200014002c0c282181490750b080203001910240040304406c40d091652201ca980c8840666480784101 = true := by decide +kernel

theorem cover : BRFrame.Cov 753417266 753597122 := by
  have h0 := BRFrame.cov_init 753417266
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753417266 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 753417266 ≤ n) (h2 : n < 753597122) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
