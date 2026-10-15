-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4731
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:33:14.194978+00:00
-- url     : https://prove2.me/submissions/c9057e04-8491-40bc-884d-e9da2bb831dc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 850719424 ≤ n < 850899280 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 850720674 1250 850719424 850719431
    0x319020f0711010905010512060a0308070b0103030806011407110102160b1201050402130b0307030f1b111605012d200703020102030414120a0c05040606030501080d0c15051e0109 78
    0x117020002e0712a00803d10b4650211100c0c40c0042c02c01e5881a0400c4091503002d030300340d5250368003810215401d08003408110049032500f00450800d40c041c0082009100940955626240c01680d030100004040c05600341076109818000b82030103046500c52001d0910f5542c0207444540d1040101d00b81c6006904c110301980c4104040c1e0b40100c048a0304605940300c0c03101242d641e440d9088210000e1510044080c1024504801c10350020b40b0180145d068018998035081d03245126250540c072490161b207060f05000702401d00704030550081c060404515194216a25402c141c800c081982d11040c2c0000c00006400c00c94104400c5048401440b07d10500d900816481c0d0550780041c0d66407041e4095211003501d0035401c800e899407222001070300b205d0a5070030340e20380e55030a01c0c00701080c00c054002c00c2c1c4140e04000012403030501c2449483d04803240240149800100040181c0d2000c00880c2d0503192000c1d41e030103042c0c90a405000300c50060400d0303414400d00c201c0c906910402c092040c2c03c0710444170705 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 850721924 1250 850720674 850720679
    0x1e021f020d140d02090d0f0615051c02040506031e010c08160c03080415020a0f110d0c11041d0d12020304030c140309030f0f060f01080703080319020f07110109 70
    0x1d074441640d5014900380300059851740f21000107418040e0600e00249801407000c1000100103060300a200700d00110b860040c03440d0f844900b008001d00c508200100e0000000b03403d00003500e09900300e10381005002e020745d1a805941c00041401e01e035103071010781c4941c0d1201a42220320390310020956025020180c1345040046218004007039501d410406001c1180040208090040e40180028099070080c02195102030b40074020342031440a5000c1400302c0d070b503902c083e90f003001c01040d400340d843c00039982d941c94207070561303204802484001e00e09600700d90b0f0b46441080000240400784c0300d00c0440c800800c0d04511064004094008946044400e140103005000000740c0001411642ca9885100405104603001609145008a41d22203030300d84a00782c4500b002801c007161700030312003c0342e00555407240d5a200588000c84420310031000c4503442040200003160701080610f801803065130440816401108200040e0780210802044441c2c0000d105400c02120a0020601c00c4007800d000144a1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 850723174 1250 850721924 850721957
    0x1031103120f0a0203191e05160204050901090602031f150f03022b02071e0803010314031e1c0b03070603021e07030e03070b0906071e021f020d 63
    0x1d511001c03001c9142c0400d10402c0c1c1c2d4000e20640b5000c2240182941040110030390040210700c481b604032044000240003541e50740d115504403060039001e858460408001e503800e01008040003400d600d09035580300158000514580015401002e11010603500e440b0340c00c0903100b080c0350590020310003410a07880040740350741001e014411954117080044e00d8108200d03a5000e08084281803440da40001903003c007542c0860f41c054442d4030b0042408024034421061490a03010308030401501203c0e052004200054565050440c10074000007a07a081c0205803410703031502c030a0704d44d00d1011154040340300340c1440d01c0803640c414680e0302c00c0c0c41880b030703020781c000883e4541100b4092070042580004041c49030001d804485a00010300155456a610140c103000780914100001d65119003d00640092a81564016a968014010215407030448103640d108149141c01d1209005440c07980243c0000da40c86031165000e04003400c1d08010540d07403400000b828142c04c1c040c103030700b0300c03d0b5140c000f510307007 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 850724424 1250 850723174 850723177
    0x6010302012a0305031b0408120906040305010e060115020d0816051c020409061a0405040902150a02010f0f0e0a0f050f060c0703030c0503040206071121060103110312 73
    0x120380a0a001c900700419200d41115200c0030a203103508200e1681d030303800400d40d1080065110300c0c0301030700507440d003602000c2110082c400d40c803032098213910401d04241460001401084000b80c024503451a007550f035541d2509650b4214031510070703600940c00405c130021201c00c540c2a2801c082c409083c030340d084200068414800a0314a0300034500044004540e01d005000711407c1a00c614940e010038901150840c000e0352044c0103904041e1704201d00010094405c040913603200c5101c118581c10107090a00340f0005020160041c2c0c1d00501c010300c0d0b02c030080310341801441900f1a581c00820040b0801c1800800e440d181c0d510780c440586070a041d4949614003103404001c00c0c4d4080206501c11100b4202140780c515203070340030032444c0980d505010b8000040001040d4041c8070791000d205c0400c06602c152410301040303d029411000c200404000102d0141c1c00d9428210000c001c901c41c03210230740c030f240e64403824104612050751100d0014014003800302c1c000103200300e00314002c00c240c02c680d260045d8075 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 850725674 1250 850724424 850724429
    0xa0e150703031d03070f020a0b03040b15040f09030f09050a14090603030d050910060f05010807050705012d0b040605150c21041508010b1e0d060905090d03020703020601 74
    0x10542d941408080f1041441d110b65040769090048a4480d8038a090036920b11045a404906c600d40706e0307200107005243d142c245c901c02c035041000421260303604041c080113141d441d00c00b254040d6491440c000081060702c14044154003e60300c1008072070803880041c0817185150003162148480f250200881340740c207840c400c45503009817000c407143e88070040400e2860040454845c041c5003441308012945000140c0c680a40520b05030500c9207550f03d04031200340040c14000c050000d8041d00000d520a400342000b008124818400081c0b40b0400c03503415000c1e2000c0364508032420700104c0603044084801e0188200220040320200110b9241200017250a80b403221103d282440210748964100014001085c900d005481030200683c5001030000455119000d4015158041020204450702c2603222034180d88001184910380a80321580c6c02805054070110034890341c2c2040303403900354907a5020720401011160070100c0d0600340780313902900b407499400c5074a0416205125460200340c1c0050704504 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 850726924 1250 850725674 850725677
    0xf031d070b070303020702030106170d030212010b0a0210050c0306031501120f140703060506091e0601030f06090e030403030807020607091a0702040509070602070b0903070b030612120a0e150703 85
    0x7030b602c01600d002c3c0c029000c0c5d110040c1d032551a10358000380c03080d10460204c203000c281303106071000c0c0c42c9900c0c4190100d00400030507105078a050401800000740540003422202001d00451b42403031542d50341101a10700c107e4a0000044011040c06050f08040010010300b00908607020440c1d81050100140c800d180000074050101c1e4803449014450200407021017441014152041e0071303280c1c20000094030094072070303d008a02120028100e2000c5441180c20013282900300740a030749034900110054103000140f0190660342c0c0c42e0014107030115108441d2050258000b541e00e4901c2c6003005810070100400c1041550040b8007000280c5074070101c0001614030749541c250304a085101c40c3d041e180240c0300000e40062600703007405004c510004440003154441d60032200e1454031151000500d0095051054141d40041c3c418448601da140180d035200c00082c10001841004400d1a0300d003112024480fa42d034640060305030a2164071400380c1d44d426109403203844000d11100c070300035018810603230040c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 850728174 1250 850726924 850726927
    0x2b020a050a140625030804030e0405040f02130f15030605010b0f07150908031f05010f0f120b1903121407030c0c0308031005130c02070e090705030d0f031d070b 70
    0xb03c4d2158841c0d220701c40c016001030950300d803044510b406800903805075015800b0034140c6c200f0f0526131609005031485903a0219070122048580d030f00f40001d03001c030321502091182c0c0380c03524130407206e21034490301c41c030070061030000d680103459404c1c824201c1d807040c2c01c41c07075000508001c41d00d050600c21044895040d031207603000b80035002180b880d10007085084070003030200074000180492503800c2c40d41c008844600c03000300ba184599402c01501c81200c02400100803c2d4140712040c01d05028a8003d0079040d0f8451010603051030b1038000407041c400078029400810340c100002d20a0045c44503194044110500344100c4000320030042d1001030280150080422a003000740c035007000807091960000b181d108486545070300307002d9035110441401340500c0c1d0190982c0c50302c0e28200c08050040c24800030081d009840c1d814140003000941040080c442080380c8110980001c2a40f0204580c10340304203250395101700840700680c0101038407032001a00701c8600d5003a903500c20791840451500c04079034012600f40e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 850729424 1250 850728174 850728187
    0xc0d080a020c0601151106090601060e06090607290f040209180a03110c0901140f180709170a032a0c0308090108011e142b020a050a1406 60
    0x300c029204100368032516028440c00003400000b075601004e1904101e4a030860314480719040340e6905e240840d51054981d2100c001081440d0049420740c4040c0c1c0040e01d814540400180440c09590111008680340c69a220503e00c2c4030b0101c80569108090742e180720141400c0c4000c4900b140307d40544040c3c0700c1c25004012840844120148180c002c420398150390304400d0034200500107080d64400668103010782c2c0e880d1101450724019007030503a61080c1900b00640c60120030702c11445080c0301ea1a03000851000014801d02c03818105500c2158140e45410343e060030516452605201c0c1c40400101c0d07032110f961400040d4000700582a0280600c04c2c240628040fa81342010f4030291810182c00710910b65004010700a03848000e01c0050820b80312204540d0307071292082d000f00000d60080641c80c0300c114082c8204856504d0340d5811036002001124040410031841c040203496010f45180c03550300c0340401d0b0440c2000d407403ca00509049841141080c07421198a9100300d00c089007910a10000418 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 850730674 1250 850729424 850729441
    0x108060708180f06060901151407020402040b0301140310090302030d0f150303020a17040b0d02070302070f090c09171e0f0105090d0809120406080411040e0d12020c0d08 74
    0x203035a42c2c5070400880350308906070b42c01e450721400c0c26101c03c1c1c0103600704000030501012000c461000c1150603500c44010220441c2e0760356054011300822a07005400304400201120300f040514003030040d07008088080345401c0100751900e1042410120081e00307124802010a4001c016030703651400c0c12070041140107510003640c008001c10481c2484407000e000c004018541c2c0050f00d8410345100e1b428101c1030010035410507025025030320481c40f4800040102e00090141da401a041c00e520034012180307403a072554100c0c000a070f0a03401c145103d03a9a6802c984d440c55001c260980140030300340341c9a1b9071032081001c00740c40f190f0800410000c00f64a22820341082c04c208041d000c4904410003c1115040c5a1002c50321640d0a904e001c0024041c500400d030300f501d001c90440da40326507245401e858140b9180064505540042c030984912481e1104802152994010a100003810385c000d010303074201c0080c0c050050382002c0030041210344140102c2d8841c81c00010900b41c1d0a241d03080030405ea5692115 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 850731924 1250 850730674 850730701
    0x918081b010912020109060b18270a060b0102100b01080a0e0c1206010e070e0102030403151d060108100e0712050a0f0606050f100e01050a1b150608060108060708 71
    0x80090a070140f07a484010195410b611600081c1e200b80b40078401c0036000000c200c0210107a4011900419032280498a500d6036844442d003000704000b807036050075440d031040c5428112030020941d6120b8a0301c10140c03003503038140b000700d0750245d501804000021402d00024180200180003c07103031581c1380c1013599400420000781010040080080801c1080c45048584508080c4600781d5518030117404a0080c6000e1110f01c06580380680c0114203042c55510741050715011200503400090f0780c0d580c9080404101c61300c500f120100e00005014552410700154504525030344804c5200c0d242468a00021201041d02030481d81e083c0d003a02d40309041800c0c124100765503045c00510803011001158200000364100320119141150a4603284048205010800d10317808000c0700000c1e01070501440da50b010308064160311000b0310706040060780b42e0340e0b468441860380c00107076848456083c010009150078001d1070094007946000d4446945411a41e5640d0b5502038138540611610300d0020700042100d91 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 850733174 1250 850731924 850731941
    0x100509040504060212010605030103050a020904170a1d0402090303040902070201141305040b0f0108071d0402040b090a0506040f0e0a0219050c010b06090a0308091203030108070918081b01 82
    0x20400c0101d0704062400078001c2d407000c0d8203071302000c80e5500000f0f0f08a0144080c0ca040301d810102800010300b00f40e00b080302a0b08024012145280e48039251007855001801805450034240c45901c501c07403050b400e206402c031180b540c45101c0e50040000d0011910080240c0d02240c0c207a101c0562101014070058802c400b0522110b0f07d4030078045110314400d5812402902250070544d420440d142005041c00040c041102d4500c7c0812000004940483d01c11184069565208006541c61425240003c3d060340c0c400d41c400703017002c00b011451242d5843d05038080401082c0888030180381a14003c41c031000786100d0312031605207026040000b011a1104d404554001c0e9280f005084d8140b003182000d420b40d08101d8070f8240b00c0d0f280541d40d08603400c0c84000c45840482c0100810400d07450b60f13a40b44080e501180445400c409201f6900c2150f11040019601800d031081c00340c08558141100341044402c4d0780007001d820459013041c240800c0c000811101c801089980c40c445015101e0708142c050200603 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 850734424 1250 850733174 850733179
    0x70c1a270109031b090c1722150905010c030e160302010c080a0509150c010b0d0b180109020d03170c03040b0601140702031b010e04051603021309150303080702060f06100509 76
    0x40381048200f540001d0700701c009518001c044100e500c238003100300d403001d810b4864a503100d4000290403000ca603680c1a900d1915490b054045501400b80c2c0c0c8450039100c9400851000c00d0315102443c016130b0003404816030281c64000c3e420403080c40c60700003c190f2180341c1c01c082c09224002850031031043c466802c0710101600500000c0910030004482d013015444112100440e51810310610b5040c6805005820520740207100422a9104d96100e1403041036034001400b169942c0e0030808006848907110f258116001344c881020341b1844441003800d070407000f00607034100802001040005600aa0350a8002c45d0a20301602c415401c0b01c22404248a0203002a5051203098068411128850501c0710300440a03a05c1c0041a03955001748004d4440685018480f05240c3c640f401020b4400d50141c10362205006100e04a540c0e81d50050080b25070100c002559803e90020903c00c1c15001030103240c028143d440202054900f007030401c110440c016205e603105200d003d89044040384240203840c0d481000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 850735674 1250 850734424 850734431
    0x2030402181303120203070c080306210303010906050d0308041b0e0420040b010e2e11120a080708060301150f0302030c0d03090902070c1a270109031b09 67
    0x900715491071500289403c800007650324006400303403106030003664018080e03511001041c0440740d84400403608001c02c45600590340076040030110b0510040103a4000040f00910340d00c0d410042558150740864010f80d02070010200601300295201405c998440d4200c400d0b02c80e14180034268000c00746003640011034292454040c032043c40072230a0b43c2d490003513134141141c00c02d04c0c0003024070040d43d044010b210702040d062403e008e128103042c0341d4030460184940c120101da00043e500090181d407100d80610005080e0a1700c0c86286004000340c0804100c80d00c5605d007800c80552006200010003031846042211034000308010f520f003504004401e081480c03070b641125403143c5540720158100e00c8164400c1c8114866540c4600b0600c148402d800d405556a20046040c041003030060b6010410032500c00766039503800686480c1c18885031a400f06640260340e0f8500054101442c01c0148210900c2c0c0301c1d0070303040306603034603038000d220202140c0e840700c00310b8038200a010fa030b0000050640e0003480761509 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 850736924 1250 850735674 850735681
    0xa0801030f030e06030c2d121b0a0903031b0b06270a09170a050f220906090b09090304060e011206170d03060503100e2d0c011e030203040218 62
    0x2194000d0b100c00091103c03a1041d60b000703070081f409140740504044042007070800c031604d045201d9040482e40b0542030341030072000401811400603e5840544a400081c220103028010103600112007a82d810701c00d60300b0000c003001500c440008900241c142c6100b9000e01d100c03c038080740095111518140d00c8440d03030307001c0d10384034071180080c00e400320040710510350302044082c9103440070040e618654a0741d610340c0d04203403000c068040d29a20280b00c000b018210410380315200c005050a91020704595500818040d1910650b042980c2040c1407403440350300090100000b00703500005031401c40c1c48615110145019050040e40c1d451030350394201040303505108010030203036541000300350f8202c5010b04a401841c07098008038200d0301d0034010700b54150860b14010310b1040c955017010a0114440041e40c2280d500245101d10ba03d0701d40302c11002600707510383e01006c1120180041c0c16104030070b003011212103220460544441e0702c650809028141e002c800315003076480d08021503d400380c940214003075a06 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 850738174 1250 850736924 850736941
    0x21602090124080906160c060f02121303080f070c06090b090c030a170a03020c060f090706050c03090420070312060f1203030c110a150e01020a0801030f030e0603 71
    0x1071440c1d21402d41444416615441910a041030f034490843c0c0c1024152035180c83c10001c4003a082c00c1c40450401020b03418005c0812900c0c49416965040391000582d035400d0391441011301000240207403201410080d000002c644c0180c80c0d91303444103102c0c09090a9aa07640c0e8195001f07501e00902400320352800081600708490340c25102c1c069840c4d44102d801c411000e100b095031350070240341d0040405850302186004211103c000c1c09140c1060300b0003500744014514000d140031700c00c84190002c802d042e82400b10a01c820301c00013001e017482d403800700c0c50b03c0911050f4641c2e0784200c21505000d10f0f55485c0040c80801e1582e1400709891711b0a407880c0c0d5610301820001c0c0720b544603181180046160030000150030300404101c204668804c08096901610f0780c60950082180c402c086081c44040404610154028000c100d5058483e1012500e09451302c2400411120075039a0691241c3c410080e0302c1c015a00010854110395200808a010003018a01110303010794010b08940c00c00d00200600c032400c0e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 850739424 1250 850738174 850738199
    0x3070e3d0210090507030215210a020f0703020a02130c170c1603080109050c030103030e01050c0a0605010f08010e030903031e040e070905133e030c130e0601020c040216020901 77
    0xf01d008030f48e403200d9003440c0110350005119030003000f40c008040c45414403070306444116107039201002e40401070610304640091540c56000000407070040c3c12902d084021882c0c00034107101464240401080850880c81020341010104511040c0c0402454005010400d4010031102441405040340050310054580507010480a0160000d141c1c00c001c006040c084030711007500d040707a41642e10000004880c6005440b5540181e0350300643e0300486501c1404203102e1b005082c000d000101c10b82c00310303500d0681d602d27003160154140703d100c5400400801d54030381c0e8000242d0b040301d14000c0d00c026268420b071410701424441c40d801080200f03000781c20403401c0380e0003985140440301d040d45e03051a2180000390110840301514240000d558031811080080c0c840c2c2c900050b4481c0710030209040f200c420404a42458000b01c1d4400100c143c0003075881b4140c1c00d1101c81c00c0c010301d0000c001001c01c2c1010030000c6d444403041c0c0b0341140901d80c00701e800302240017620000e1300c020b50040c0401849586030740000c0c840 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 850740674 1250 850739424 850739429
    0x10090222052202130902180f09010c08010e07180924060503040507030818030106170f07081f11130801061509140102010207020603070e3d0210090507 66
    0xb480352503141a4408a988000c01d5145a4010000328141c440000004001c292943c010380e080000458003110b1700d1a441100d6000740d4900300646c5051400a02d90743c2075410070914003040004c44d000400101500216440d0401c0b0f190502e041c1888541d040ba46000744c469118050003401c258089071360340f5106c0d030782d45100b43d0354031810349803191269800d5400788003d0f5001006944000c80400210758144054080600c914004840020158000a0039124207400014142140250382403ca041c00c02c40700d4401107a14015003040c2d80b61680242e00d40d02c1d8a25040211001883c820341140c2d12503115608440540c1c1c101912110340f200f20001c1a1070328011089030350310341080410070a062048581c0382c96925916980c00d40e040c0300d43d00800c1541c42c840e41e0305664080c0010700041e690b04014510404040c1c2c0c803580290261000c110201c50b920b21205d4414480e17400411070710600c0c10510b01103400021000500d1103141004030702c3e115440c11300d00082441c110b0900100000495146c04 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 850741924 1250 850740674 850740691
    0xc0f0417070603110313030e0a0305100f090206070f0606050d0302240108030f0c0a05061905060f13090f0206031014120715020115030804030b0f04051009022205 71
    0x10550700e9903030a0f802c9500441200e00203820520002d02d14140c1d081d20901d98034400d00e0215104110400411004101c0307801c202c0e01380d048810b00b4035141505118400d2000324003031003400620700c90b80100e0080c0c410380c080500101e082d5501003050202c1600254020000940f10308003400d514103000f5100c041d40703004140c903c2c621060a080103040c9044044c1078405180103145450b030702009200c1079a200804140ea2402298007003000f09800f800414482e60300f401c4502c03200507141410300211040107240c40c0c458520780e0300641850700d13250005007441e0002440010305003001d04002040280d100c0000354061000010481d03c101c2c00031780c441c1190340c0c40e0059215900b510041040f440040003210650741c1c403c41c010000c00c0e406003c0400e04011a000008400b803d43e0511050b43e4840c5d0000e80315250001020000c11080001191388200d545076500b0040c01c00d561019240c2c1382c6050b80719042e0340c03100100415580c8081409040c64a921201d4100c076a0102440700a480708aa0a80 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 850743174 1250 850741924 850741933
    0x60f120b06010c02032e0606080115020303040f061109030706030c09050406050d0320120a1101090b06041a030f0a03030c080403090603020f07120c06050a02130b030c0f0417 76
    0x82195000d0003c10f10307a0765008000c0d080c401d049001c5601c05035151314400308001c003283c00d920412112441000c02400e15035594032030960605000c8545c2110040e0f074001154010070401000c541d022101005803640480041411004a0185021400751407116035241c040c400c07001401c507402d0387c00b6019030f840d242c540003909583c500402c4122455032007030075049680040c030003000a1241e02d0140109041074403074180d41402c03280640c50711000b006842c40341c40c400075162038030540000441d03145205441c004d01c4829102c2d550b4555100010b00000d02036a160314802c04000d81c00b481104008a0180480d84440315a51031507940c1d030900c1c10140c000c6880c10b02031381c0c80140f25103105486240c01d9100c01ca40b9910740b04c002c800a61001e0201c602d01f0b84248002d038001043c007030510500074107940d02d08060000e6400d10104507240a0480c03c01103104000c3c980c142680c00350301d1012990041c06958403640c0c1d5050002c402d1060301d00311480c402001401140c0c66880c070000c2604284081e0855 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 850744424 1250 850743174 850743181
    0x13c090c051e2b11180114040614102016030b0a05070f0e0a0302060c101104081009150e0718020a050301090e0c061c0b0607110d06060f120b 62
    0x700016001440041600d801883c00030041158500c2004590b003002c1c24030604004c1e112000268800300780c104031001d174016030500444d4603082c0a00b0018180007803880301010f05450005a0b220280c1d49244148401540c2448442c16100c80340b100c0c541000b42540d1440200c070103403031038002a5020884a042461003c00d408003c903200f528410301d26034031400705543d0119070540710200d000455550200507100040010b86484001d031040c444000c00400912420300242001e6901400802020a6041c00200310300c0d040000c117555503c0da26a000210300e0054208402886a03409810001505000d001e0080c07210000d00c8500300d889201c40d140d14161342c0c6010400380d204084e00900026030600060100b1107680d031010380c40403020000c5890755200c00002c00d0440c1c10290202c00c080362240d04c0081d01c94041c0c0940d10116508807011450a15a0703560280e0302000e546115000c0c401c202c0301c1d4001c1020651000c1d003c2d2092800010b00c1541e18141d0200306603014904840011150300070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 850745674 1250 850744424 850744459
    0x1401080f10090209040209090109170901021507020718020c0a0503070b010b07030903151d010c030e060f010b0c16080a1a10051507080c013c090c051e 66
    0x408641c01c0d40108180121740f110b0f001c00881d146c1c080d0464400355a9001014000f40790700881d500140e60010044c3c0d10748020200282c282040720400f031000c00002010044155030208010b815945200089030300c0190580c40781000313000d440f140c0c1200340708aa0720f0b50b082c002c00001524205100300f01a0400c1e82c0c9660f0a4081400342c110000c0100d5005001480000e41c950032182c6621000310f400070741402c0c03d040c00c0301040f410008000d01655541c2400307421a0303241c0900611240302400402480c140011910031000d0b051140d822046004261098a0385050007040300d411808000595010b0f128000541c440000210403110f901007045254038071440310042d02e202e4540d160402d0455072903d81401f605507841c00f01c07801421390402010b400151024003611210750540c00016920f04c8a110043d0b030445654042582004894180c0d5428101c10030b50b030003088a40c513404610100b10f850101d5803442140c20055206203400c1d1303120403100342c04a41020024044034140c0180303112924 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 850746924 1250 850745674 850745681
    0xf06010806180a032604030c0c050a21021206090d08010e1501210213231e0a0f1401020624010e06070f0533070806041401080f10 57
    0x140c03003103150030143c052400b00b4040c00201c0d00650008088000e404d02c000d50004495104a8040300415000d00c00c5605112039648600e01030b11042d42c2c0d00c0b02090400040c80940c0d0b9449448650280302408420f0071922491503030441d810040341100c5041c10511403031038a9401841340c2c4000102800d0001940400c0c4150071401409101c10240c03461440000448228600b0f01404d20064a00e0104e800c843c80d07284010403034040c3d100414407000d0709201c0070030031110b6540f5404800d00c080d6001c1c4a004d950302074070f440520111002c444100341440001c00c585501d158404c039100c4c50700460008103107012042d0107240000903400e803078084e03035140c521955000c100601404000300c0c0d03840000580d4010503001c3c0901500820741e5080c1210340e61140181241d4640440b603907003000c288007200c1d900319042d03095401d01c122004c2180600c5000380420070a4020100c504100001010a4076034440360300c51083c0340e907490182c44056031030310310301c6035100d00540c0508983e224407001034601030068403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 850748174 1250 850746924 850746961
    0x20109080f0a0215010f03050105060a050609120705030a0f141f0b060f0c03071514040f06091505012111040e0f0a110a0503010c12110c0f06010806 65
    0x205598140300d040c1004088580000001006611510036584c2d5042081a1814001d001c030454a8a84a0652404900f2340d80098240c2d0f0003881740083c02d0059a99003000c2d110142805e6444500c1400c000c0718061a000d0b05038841d03905405002e440b00207000d080d40d2059a110f014402070b111544000490558400c4075200d0080c0b01c688105a41d0b100001c00d0300101c07188440204024100350720101d5101407944490344039101684006031680801480c040f01500d84040350320200807881d60040105045080204010310b0200000410f500300152507108005150f081507014612001c15800310001386020b001d034a07510903074940049402902e04c1020000c1a0703010004005043e01d007000d00c8054003110034441c43e2809250100c0c038072034004001e030501e0719008031005560415003c050040104081e00114080d9050200c2101184d411600c4941c81d01c0d013080d80041d603041451101c0081c0c0c001d16200c544079016040a07e08072070320004000e41079640b10026208e8545070080350001518094 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 850749424 1250 850748174 850748183
    0x3140307050d18050a0f03030212180907210c11010b030304030b150303030a0f0c0311070f1103030408030d0509010603120c03021c08091e0c0613050301050f09010c020109 75
    0x389031a9030b0440c440c82031070b043d84600020b0791a00340c1c1c1300c50009000808941144d080c10b590404200b06040d03040040314101004c000c141864051455001d41c410008151114054181da03000708080c84d21817101100d01034401d101641070307440031028036409881807131000e20006292043c40c3d680500e040c40b500c8038080e0001d0007580b501d440d6594021044100070060688090300b000c1082e1643c80a000540c401c4040000c0001c8508100d9103400403039107560035800030980b9022062040d43d070f140b011203901e90780000e000c210891061801e110b0345098250003903003501012070001a0481e00101410745c1040c655001e0250390b4501d00700ea800c90384180b0001d0700701e00b1200d5210711300e14001c082d003610150081c4181c60404c3c6408c4a000c20860020580b000080e4245042066a0f0b1062016860010b00c840c88401c1001c00c2c0303095650b0380c141c03032001c585c40741310000b40d2254800403004550b0028000900280030914042c0207a01c01c04104554110240d400c2c803104901281c41882500c6540b03521 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 850750674 1250 850749424 850749433
    0x191b05010302031e04050c21191211010e0304060e0a0b07121409040513140706080105040b0103021c0501032901060c050115030b0709091104090905030409090308010314030705 77
    0x2000c1c60030880100c003030005c2c6d545000308a003512444e120080038240c903c03001098503101c7d2800446031840c0035039440203011060210301a9000050209040744458043d5107882c000010001000b20700402c000703c10510140310015000400d207800400880240f00211014031000341d407910941d1141c0306140b0014038100f440c0402c18202030041230410800c0703c100d80340504080d14500424212581a500700c5030b590804030304882000004201c4031140717801040507100103858800094041c080c1809028840c5880d110662040d0744607506031105c0c800743c03035070b1590495601c11210001b02000c0c0010b5030700311041421108040c102c1154944070090800c81c42c0c0a5078070309041102d096008050881d07541d5250448505d03014010140007010b58040d26103c1001d040000380945000350a40c004201e842c20038602000000100c07056908403948604040380340481ea151035800c5100d96040315008602d84540501803561040445040e80c0c40341b06103030100c40d46c1542c01580d81c0900c9000030450f502 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 850751924 1250 850750674 850750711
    0x601090e011113090507051303050102190c1a07020a0b010b0408121215011b0c060e010c2402070c0e0a06062120070302030c1e0a0303020c191b0501030203 68
    0xc035580200e0381b140b82803801604080074100c0511071038049500542d1140e40100301060341c04201000b91001002900700822502025074031460040311540b002d29180c3c0c4000f000270b8006000f44000a06030b513001503141c3d480d60315040344840c0ca401c80d00905605201c0c0300320702140942c0314006c681c0300c90702d0081c080c03502d552010900b2020f5903200e12078034104240c0d2641360503911045419100020b2099810044e66810440d0081c0300c4490900c0b4903041000b0f00c59410003103a20b210030000303031b1600324191030b15130a01100550b010380301380f40005080c0c0603c6c51001410703800c4401540d014958900b014442c01d565600120f0b920054001d0b008050020302d030701c0003260782c41caa10801009040b41c1134880100403070170b00007030340750422a010350141c0c1001480446010302404400b40c07040550342161598103581d02500d030380d80d0700c2440050a2540c0064a03146a04080205c0d0f90107401810082081481d030b460040c41d03840094038070f03805503000358001107021340c064025a481140c04000ca05103646 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 850753174 1250 850751924 850751939
    0x3030203121911070b150a0303050f12070f0801091509051003060c020a0201080a06140111030d05040f060f0e03090114090301060b0c07090c0e0f01030e0601090e011113 74
    0x720141100d03504650868080c62403004038003a6801d103042c0700b0011500d078085410640175051006000d12441c400e5036070418069a42c0216180940ba00b5180464990f0141fa800315624070600f049940745100807020428101d610070000100320a907035030395800c41c0c0d0ba04d40e404004d44000410083e10380f00350a0701400302a40a83c46503601100050544103115501c1d103e0781c00b111140720140300141c2005c00700d0700c295608081c0c0c1030f4004000300002c004c2c46141004030030314507405065036270401400300c00f011141c1d002042901c01e10b10310000100302c0341c2828278190003d00c8030100102c1c0c4490900b064182040d049100f144c4410381c4500c065172078440803200440d10030220b400c50031000c00c801d20045100d034400340700f00e07800340021403071855464030038455a9160410b00d5016400103030504003078050031079101c42c1a030000b00c0140ca4040c9210038480040e4050f01009441d40c01c1880750f8000060644902e8100303910502e900002000354110b0349a00c648103101ba4000c0c0c28100031031394400c01050 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 850754424 1250 850753174 850753207
    0x409080a0210022817010b0405010e1504090507090b030f040b0f07020a120210050c0a1e271508061c0b1819030201060302010e0612060904020406050d03120506090103030203 76
    0x741c070301e05081242d0805c1c0c076403500c1c0002a0082110240003203414081c82d40c12a206103450501240c081025141d9114040303864032a50190501c000d480d13001041141c9d010320840c40c0907010ba1390b9807980360701c0c00c81e0b051728a21798121001c1e41e8400c2800c0102d410103070403a0119000d4030899020307001e0710800e0f49800d10303108414001c900442c86824001040424507200d1640070700301204c001e0390385641d5004000c1000e0a1302a107100c0822580c6960a50203400030308001581003030343c8003071225614564103820410740b26400013080708842c084500341282d0019516200e004200e13084a1500c44c001d18903041d51520000041c000361241e40400c1e4004d40c02010400703194071245c100c410342c20500d00340590140d207405048000d40c0d1640001c0c070456811480d8450f024000340e85003410000ea5421a00c8081c0024007818022043d55000c41c0964035a5040240500800740c1450100c03649454010881c040612010020380e140201050051800c071500604903901503000314185001c1d44500d0068 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 850755674 1250 850754424 850754497
    0x30a140712051527011508011415040b04020c0d14040b0a0c0602040312020f06010806061c14070b1305090114011107030b01090c0f0c2f0409080a021002 67
    0x104028100d50740a0460702881d44c9043c41ca020000c6a901c0401c03015548150840c0c1250403e641480401d041013104089440d900c090044640b50842d420341002c1801800c62410103a0414000104070050020010b140f0340404480d5441010640881e01318080c2030045004070071311701c00c08001ca04680e074810300d0031400340c500804c00185060707900d540b100d01c8808403410810251300560a0800c0c800300c14000e45004101d0305000e011280b40590006400826401048502680b2054244244089056981c0c540c49212040300c0c01c1d80d4803140b42180d260041001c00b0813030912000c000ca51810f00d006054101c440101664005440f8400150749030100c004d048031841c812242c0000200e8982030082e80207081c055000a08801c924400421520100c844002405a581c0504000460480c0840101c482c1c550700c19100014140600303020306052407407981d0080c1442c644c2030034414104014a0f045001e074089441c842c0c11100d4200c107a024120040c64a502c40c00c0e061017641c940705c1c001c0201d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 850756924 1250 850755674 850755691
    0x120305040b0703090e070302120f0c0705060a0204170f0c06030405031303030c060b03150c0a0201060e0a020c0708060c0409020a090918260720030a1407120515 70
    0x40c56220700ca4240c003600400019000907118040820224101401c00d0fa0000c0040c6400d51804500d200301c00b22045001c0c22000581f000c44000949403142c50003a1072081d6071082c180c450501303100b000710000e0342007406038424250618280300c00031440000c03000001059003001d4540110804d041203a2900010016100303800100841724041d1805502c80010318840c3d03d50502102140c244481250508400c89000c1e5004028400502d00d0f070420b10f035030105540a01030760782c40d4a02c3e801c90140c60564004141541c01c031041c0120502250060441510441c040301c030021340d15100150f4130361054030546401c210030031060001070650b40062070b0045042c103082c1e10300e40d0b4455051085441d4015254814040103400301c1c1045031745080800750180d00400400c914428004000d000e2080b00c10003080115913245200c01d1498040030a003080e10000c05441c01c1c21458206100312681d07580020070a4025200d0118a000080d6002c05025030040000c1c1042004903180040c4050060517403e07 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 850758174 1250 850756924 850756927
    0x1270506120d271d0a06050a0b1b010b060315061213060c030209011202030402041104030c060e010f0e0d0203011e0b0103050c0c06070c260414030d0801120305 70
    0x120200c0c82000403440081c00c81d9103100e0304004080b4840f00c4460744425003040202414810044404846441300808040d81d65000190300c40601d102e0051100354030a640003100003c001961000140107009424103000240c41941c2c018000b80342261a502002c41d40403e060001c2010703076003c44a0f0708200b0201404c43c41c43e003101121071610004045400d60000c0c046032451404006007401400b80b03400850605508110445002030001443e0020b04006541d0210001d025540e82d07800000d8401d10090a00760741d00c2c0c40341801800703144140a404041080c1c1030b64610307694441c2240000d4411035980d0340124800d00c1c020000c500e05c41840581c1d040d9240d8030404203004c1e1540301c8200c20703040d104000400704107240016007074410041503000008000c0c09450000c1c04089000f03580a0b03124500740c11141c105180150700c8019010341607401d148110598031485111500500075288542060f00c00c02069004140c0c0c2c1d80b200e0006240040c1c03840d001007100d421680c49904000e03200b400c205 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 850759424 1250 850758174 850758199
    0x41d0108070b130317190c200d0807050a0506010e280e070810060905060a09180b070905040b0d120e0109051302071b0b0a120e01020c010e0601270506 66
    0x500b0036009400f640341582c080099440e440c2c24036407007490b02c50340c200e062001c96500c1030344403230500c2c03a1124000c1e0800320804258232141ea89408518403032031b50044102c3c0c0c0342c3e2400d0034480d0f910360600038202d4003072107102c0002c245040001e41c994031a01126072070300380c00c2084d03070307013020005a0f1181030000080d00c404c12040012030134400b68010f0a6654018800c80c5101c41c001000e0b2a855404030162034504401c1c00000d445180008056642480001c0340000e03e020944030700100802001e050010280240854203602201150859004550034000c1200203c10403800c400d0601c03008000031a07806441080600400303000070854814103181d02407564800115803070880030341111603d00d46c001580401c00c8000c13017540300c80b07021000342440024186951150315101c0d421507481030001c0c604001803420059004007800003007820003551100e0000580310302816000c1c0550000380108800030403480300700c05468040e140444440c9515171454081500200005400d41d0741140076120300 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 850760674 1250 850759424 850759433
    0x2041a09090f1011030c220e041505130f03210207200102150c040b040305010509010b1c110d080c1c0c02181e0903041d0108070b1303 59
    0x228401c0d10000c02901010000807909030802c07800341d8501c07800f82d1a1a503100100384958060b60b50114000f0304241c0d9410f040d0540c1d0301e00191380711110040c0c1801c1d10000c55802e40040d800c03405144500c6042200e241907580303510680c0d10407200400020070700c0d20307000d011584003031840007018000d09082c90710014000e42c8840b1030709400c012040701e81e0001124810010750265124054041d220b40440c41d07000c410000f0349402e1441418072201102c1000b081c0300d40c901400f22401403903203940c196501c55403450301178080c0500700d42d200c045510784204080746041c42c00007081c00700207560a01d207031740341c569550090824203244143d40000603c0e0500000a05440c004c100044440c0300800b03509501c18a40546030280e4103040302044061f4001d9001602e40051011030000b288464403207543d101c402c10802600744402c403034008001ca10a000c20300f0b40103c014015244415055034461125050340c5a22640c02e11982655a00c000020048a1408000341c04000b03141c0000b100c0056582d01c5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 850761924 1250 850760674 850760689
    0x2100507141218031204360b130902060f1e130302031605090f09010920010e0405160c0302030c030d0b010809010c0906030c030209060f0d1d0a02041a 66
    0x9882d24034040001e080040300341d80c00300074120b00000314020035401001806900182c0030b40c1c890803003101c103807040450081619500c10f880d908951580c0032180404440150040d0502040d0280501c0d1000f51420260025024030842660007400c40b52a04004140856491f803040501c081140440b16800325135200b400004c2018410108400f030320703681140105810501811068241040384002c00c111030340325202e045a00c410301840d074807815030f10100e4450250916100c014201051130003a02000e4000f4100b003040712000781d070b0740d00c40f91500a0600040700c0c1c06403a0a21060220f040c401e03880d6128044555001c0d10920603a81403ca11004240c07950300b26001500c2110f0b02c80015982a50748103604a50020b0804024004030100c01c80240c5501c5d054041c039410541c07a580400e18071802074049440e05000174141c4c1c2d94585e450403081c0c603640c00a08581c4403e80c1041e0801c6006030181aa41c8000f121140140144800c03580c06c0100805c00c1100c800c00a800d15a00105150f49028 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 850763174 1250 850761924 850761943
    0x30e0a09051306050112050c0d0f0203031c0f060807050d0203010b18070210090f0b06120304180b18132d06050624090a0308030c07031b0210050714 65
    0x22228580c0030514040d029244160030039081c402039a01b1200c040f440000e0043d0785220255406202000c42e8202150090602a80a9050300c0002201e07900c410342c00c0011070050f10000300c200b10b0760164520040684009105440031544400030034446440c09402c44201544020000298152081c000c1580c1c101c201c02d0005510b030700b440030002c070300341c040c00a62583c190307221080040480680e90600100e10f400da0203013840424000060950310381044d8170f006509090110781d2600c0c1e551004600c1c000444600440c02420035103106840d04181c2c0302c004801c1c6100c0c44c00c070406d9481080300c00301c5110403441aa0f150300c40301c2c0c1d0503071000c402c0c500300310044101c92402e13000c071091428000c5c25910098000e6000302800c641103041c0102541c500078450031190b02d5182d03185409000239070070030400d8001816540d000070070f0100b62107900e4020090a440303502c2d01d0800c0203864003030032507800c01c0440280d000701403400700c080201d201ea801090183c2c451910720207041e4481f907850f8039050405 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 850764424 1250 850763174 850763191
    0x20c150c07090e0a0c29090f13061d0c070b0a020d090c14150f0a020c030609010c02060f04080a12021605030307200a082a0705010921030e0a0905 64
    0x3d015909022075020980c001e05106e16403203840c071044006214404201d8448500392000102e2020100d94641082d6240d500c00145240d00418008100100612040c4110912114020340f48640303002c214003014070901c440710b98030703080c03002c1c94551042001008050240c4c3c80d60070000d0a0840010f442195503460140c000c44044508001c4440e0038240740302c003940e05c54502c0001c1e20400b50b80f0340c000c440c584546403117050f407500b80c1d10f0b0741a854041c008038a240d0501840f0100714800105501c0503510840607821604951079000401904000a540c081c0856004100d1031003164000c40314452564144a001803410b00952002d00000460000807503440d00008203100e01c81c0d0340070418886511400d85d03090713400b90584442c95921400c50314000c000180104142008220500c01341c803e00d001c0c81f40315464801c84480e0300d519441c0b14060680031402d400c030041403074140000b803904400302c145245103043c04681c4003600c602d682c441c1480ea000c802010302240f51011070081d41e000d001107 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 850765674 1250 850764424 850764433
    0xa0b0c030618091b040b0a0605090301020409050a1a06030915040f0506090d0207060215060d061e020d1401380c06010906060c020303040e0604060521010c020c150c07090e 75
    0x1044e0820f40b400f01c4005075500c11070030040080520754800c1d149504544035070074031315641c0c131551020a0180c0500e6110304400c40c5841d080144684507a041351408101084910801040301c004000f6140016a10548a82e0191300040400340d2886210350b00b26008103800c441c0e00c00155506881c100085842c803850740c01c0040071202c1180c0400152001c0c000600240400b00720840c5202c1545400424803481030b500c0c000014140700c1240c0c00341d9135064803005000c00c1c80801041c44406540b004140307640040c50243c03034a01d4611143c0d2244d05031402e802c14208013402d240c1e0300c44418500f20040c80544084110950311360720000005200843c2c41c100035081e10340c034141040049803a194440000e104c0da1481d03d00060b60040708413002c2e0350503540b0211050315000045001441c050300b14a401402c0e80350749100c00c52050100c001c1d942c20140c000d00c0023440095040b40caa40785c020042d500b019032a03039201003010300344001d0000c0c242c4100842c1c0c062595443c1e860203550400c030030001e19420 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 850766924 1250 850765674 850765693
    0x21911030c010e1014071a0f010905040c09022101060905130207031407060e030703080a0f0c0e0f0103020d151703090a0504020a230c0705030a0b0c03061809 69
    0x14184984658088242002240f1000d000d0205034148005038040301000000c41e411018080034900382c403001d9400c84001c1d5585000b032028010700340310584801540b07403006800083c0400b0640101449590702c45441d030b91080c64080d60b18003035000f5180600d009030608010b48400403450800a001b840540c2c0d8403142a4502002e100500400d0f080150714580100b08090119812202c0079405c1420985459940c01d030707504220004202072140042203000018a95003810ba000c2c0c0403c0c010005c3c1d503020400c005200380f689044079001c802c4040811142c07500e401140c03502454008c102c0c03006040252900f500b1120301c604072205000032549114100d103050140c1070404421100040550004500e08103040300090710203c1036101d007521541e0001390010f1468401c15a403440b1142c05580e040e5851800c142e00f04240d041040c1c40011846604000222840c002460440640d0003010f0f8070704640300c0103991904c0d584014445504400c101000108a202901072103100325601d8001d044600b2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 850768174 1250 850766924 850766929
    0x70e090a080d0216110a080109021f050c030403060b01030513050c04050615031314150c0d2306031006060912020a120305031e010311120709020a050c0f01060b0415021911 75
    0x100c29410204040c9c7c507010401d00107846012209141d00314206000b00d02040c2c82004131564030801e4400013450001080c000108103080e000117104401c2601d00384529078030a0350350b00400440d4403002d001030f4020440d454031800c2c6a17000340d40100c005003000b01a119071101c803404992041d07030446c10b40504800e81a051020b01074580d10562106400fa185004180d11200d40c510030181042d020042c0000311100d9591460340030380c3c0d0000e5942122007a400030002039004440c0300301c030750320f0090041d0900242c1c012154811501a1100d0f602c0b81282c3d02d0901100708100c0b00082800ca8104507031f00b20100e07200701711000004c5064440d5880e0340d80c07481c0951464000f03ca00a402d614840515001440003550920200034044400c0e01d5118064190069072403400030607a0040186901c00120390048661000090540fa0080c4048a000c20711294180e030803180300c1d1107401c00c0080c09010030300a00101c4240c01c1540d0301d440c41181d10f840b50111100c25409000380301294111f44904c11380301c050 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 850769424 1250 850768174 850768189
    0x30e013b01180302031c0501052d0d0501090b07090b040909080d0203010f17060f16022503050106080303060a0302010f030906050114031b060a050a03060f0603050702070e090a080d021611 82
    0x1184c1b486d40a100c2540741ca030200d220106820502440c05003c15202042d80702d0f1100080e81100d0010400b6010311a2401c0442c001d00c0450070994405021100242d5031034045c8020900702e03510313910310620b041c0c60035282030002c1c46441e908651910b402c000705401c8a110380007460107800c0421405000519221031800c103800064080365141d00190100301c506c605140c10540e0080d0384032002c01961f200204128101452144000403044034400800001172074940080c00b034038403d03802040303182e855401c40b60b5030b0f01040b29500d901c048000010310042d4464001c04411019900300400c100d19207903581d20607107a090300030701e901da070320600080078618040080100d2464071461166003002d50101140d01d620076a2008418010000b42280c0d25500c00d5202c5001003031000c41842c5030580311a03004000d400196074450042c8509003000c11a40d12200d141806840728200501d9052040da4030603805421256102d94101d03400d11040c05085040742c03400e07040e6441041003107890892001001041d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 850770674 1250 850769424 850769467
    0x40c06081303020607210906050601110a021e063105090601020a1704080a05010213080d080103230307050c0a1d19020405030a03030e013b0118030203 66
    0x4540c1803164401080c0c011031010781051140c070b0a002a0342d181c0c0100341c0c6c145e52602c5c8115001d480c241f810001d0010342d90002e17004400036a42c0111940b440c000c02c0d540e500040030081c0d8081e0382082010b981c240c181074090030b4000c0c0903100c00c0c00c0c04030300300e03243c2520354140d070400840100085544220038100e01d00c68001d07140c100c032015418203001d80001e558010401008000049203800c2c0c40282916106031002498040c00f00c5011006619245001c0d40100c8501940e2610b100c1e804101c0c10800f10b0550440340c100c3c0e4401074168a503481d042188107030208448a1014400d0401d6080d110900081210034050b00080c1444004a800d10030007080c55402100c82c00e40b0040d204400306800311455412900c05000140c4001c80000e4080c0203104540c0304550510448070724400301a0140c20081c9103144e510000c0100c0f01a40302c1003000058111001a02d1a411640f07050004102da905800e00c0210341c0c000081a000810440d42803104004054001d40d001044107003300c070150000302e0b107 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 850771924 1250 850770674 850770691
    0x60e0a0c051e161b0503030f0a080a021201081e0714010c060f1d06010e0c03040221070b0c0f0d140304050a06111908190b0f0405040c0608 61
    0x26669012005006006040707040c070a01525203448254807218906943d040e00d03101d0900003e016903882c1c2104000851800036035100c0f00341200003294500401078038100030740e44280700e00c0c080c61004107c94a980003000c5100f00d690a020016540c04907014441c0600703000c41c006c0100d18080140c1c9410412050030b800f44c1ea03480000184043d003143c40802c0214007003800e1031010500c01d4a03200e80600309624485034114030304148034041050948213103070014508001d440c0c040c0d03212100da020b03802c0308a58500b0540800c00c0410010b0805001c030a00307104240034040130070221140b42d00e080250035880b0640100000c2101100c2882c107000c02d9600c02c4000c3c000340a01d050924014000d2015000b19081541c80030002806101c0184503414840358044000c0001c0c43c983c00e141813441e00a40030500c50072207190314010b03809008480d65030150b01a502d4216508207000401c0c80078240c1c5015040e0408940d030744e24000d40d11240a00c9024911031114010010309080b002032060100800703400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 850773174 1250 850771924 850771931
    0x617060421030f0203070206041e03050a080a0e07030605191404020105070c0b03010f0609050324060a030807120f05030c0307050a030e0a031116050310020c1f060e0a 73
    0x1001200c50080003140d038540040c280c0720840040c1c00400c02c00da4102d210034000801c001040360701007007244c40343c1d121b0f469094904940c2c4c0c4c5e81d030b00000c03004140100803e504100052481e4000d2801030b5020503080f030301042c040b50600015050103944d605c00c4a815817204244841144211034216a807011580e080001070010f07407005011200140010303050010004441090015401c04071000d0410150000e40d296561004001080750b035204072000100700031804a224036000c00c0c0310300c07041d980600d103c83c02c1030112030071000c103a0041c100c0d50380880b01d03420000009881c3c0c1c02400c0d03100d0040307c0c0540ca4145031000901890851038984081210030420098803080841c1600c3d0400090314210303884680d144001e034010b11100529601c80e20985421008040c0c0c08201c8500204021003074030f002c504000800d015100039800303103070750681103068200e04010a03070f4017921080c64000220b07444841011403a940c07898540300c00e0200641c0361a0b0502020074414800350304060f41c8041007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 850774424 1250 850773174 850773181
    0x3060e010e031e04170a02150901080a0c180b031f05090703050403020705060c1b0a1a13051809060c09181302040c0e090606041217040306090303061706 67
    0x203500c91086a00030322403828407441d442a6010500b003a200070344242d811107101044c0c000c1ca80c9584019485040b0700c140b1003000e41d00b075410fa140301941d20341c14041c0c4403c807480d140d14428200dc0d100600621040003500c02d20000034883c448480da005210381843c41e076990130301c071071089045001914400c15440001d03a080015071505202550320803654540081e0b142c44500c0c0132410503110b5445030703500ca500460760403405200840d2021042100d503d19101c105091400e000c010102da00c980c513481074107142005105005140248240d0400301b0611440700e40b200b001958040074400c000c41c0c0b1075074440c10801140400c000b8660840d072a20a10f0b8242141040080c91a03e40076400313004444e0b407200030891201d6000700300c03c0c100c1e0307000307100744180c0460740001400340c80786c100b54622804401c004110103040c00021034064030360344843c0e0b07550401a92900085400200d0a488010741c1c1080000081000c0c0d2041810701d9100341d5001c5219031510030903062009829080744071980054051 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 850775674 1250 850774424 850774451
    0x40e01051011015417040332120a11100b0a0f03080f0702030f010509060a0b0d0f120c05031309320916031101140a1d0d12030603060e01 60
    0x136001041c110080342000605146000701022644004643d607601020802004104080e880840b0f0354601111000c0c4850380c040348a918815907a00c884143d8010360380d48030b580803600000b400d00d00d03010306018078040d001c000c1581c030f01106040e907125400d42d50442c1d44518035201c01d10760000c09203103142a10f51030440e00c690203d031180380c0f0560b41b00c2c0e200042000131501d0501050316a051000020400b074074044d009183c036500200c8011750458030b03040401c07415240c010342c030101d00341d080b05c070203e42804190340c0d04000d80b2380762030b40001f48500d01d0580000100304000811000026114025619184c4282c1901b91120201280c0782c001980e1a80008624a0566410031080c5a06440181d844554200d4182801e1030504448450b0486010060102180015580020070380c0c0e44041c4c2c0b14854100f203000e004000980000030b250300441c503171958519000c0e8158502c010001c0b50324082682d15944144041c1700c04802203034039210704205201c1684108441601c50000034401c4441c10040b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 850776924 1250 850775674 850775801
    0xf08010f050d0c0b03071e030207080d020a030b1507050c04091128030c050f03010e06070c02010504091410050102030a170a0207020603040b1b040e0105101101 70
    0x541e402071100740c1d0700e4400d1002a4000c00010071a10080b00d0b524180380070024014202040b00c00440c0041101413005c00c2e2180c82280d009a400c203030540c0c10000f04004035006544103008180405843d090b04003003540ea40d618002c1e440d454825155959481032503c0e50504400c4e590940c0724074035024510300428100c107120441c1b00c1c021102e90301c4140c9a40c801c1d40a4101240d085540560666808006c00985110741c105550701100e6500c1450749001c00c02d4281c0704c1d1407030b0207030031a001500412402805140e0040055205051080c00d141c3c0780c440c5070040355001c24001c50754403040014411854078403401c4002405080c8065403402030500b801400c454a0b1410320002c2c2d105500019105084c1ca90555400303540c002d003907654a08160804031080394041da020040417070201640f01001c0001400c480850700072030003c10690f880c0a007000040c0c0d02510100061041001e108220881c081c4283d5824005d114003003030a6a2a0040104500d0081104188240d60240d0b800d10399881004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 850778174 1250 850776924 850776929
    0x2150f12060334080d030f1a01050f0708070816020420180a030c03050d090f0f09021b01060e270304170a080a02071a0a09030b0711070b0a0f08010f 65
    0x500b08500800c404140300d0103204168040304c018016122811800c0394542c2010313165161422060160340540038456454900911035030380884ea00700140c0002580d50805800b40500490300142805000c1d01c5050f0240d01003a28a000000182d42c1c3c0e008500c0e0621810300c51740d11003131400c10140700451b551503480c880c015406812011150300345086564068040026603070045410008030b0352407808a55807501d00c0c481c03038003003002e420010a102a00c41c100600300c41d4200442c55070302d484d00d000340000354071039009a1401021842210081c0009000b0903000345a801c00a1082d0b280207060300203404120380c3e0844000c40e1110f080190300c18008250b80a84081110110803400441840d5282401c0c11100a00703143e80801e011020355000702c3e040d0100c407001502501d1016070712208001d540b081113400c4011400130001400890250a0244da2213800b0742483d8824507819440549403108503031007030703800010000c1e4403212168402c06070032100b02c00d03007410040c139418480480504103560 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 850779424 1250 850778174 850778233
    0x40c020f0d1d0616030201050c03090345031e060402150903120406020c120a0b04080c0a080316020303010602070312020313080307020406210201030902150f120603 72
    0xd0246203030200b109042916011401881c2d5a910203280f42034441e0322141200035005946403400054006c0400c2046038400c10801010711326007070525004c50b0f00e00c0440710f541200c040000b00b0350021010030700b4106544480e0340f030b00f46500e080308008140c07512150000b003219a5524a807040b41210300041c141f0f410503030454181e04800d4034a4010120741c09051a103561610910701034a00240c1c03040001d0003504e00642c00e4402d154020018800c080085000c001c1140d0301c014409800700d0b0002d40101d420500c21a942d51034003500008041c90070134520780c180d9001d84c000050104100d5600380251000c0340c2800514110b6241c144041d40701d400e00e11015200501c55210280051f00c244100d9095800d001d00c6825266152110240c1e070742c001882c228040c41c9041c1c00072504841407030221446402d03074400d00c6012800b69004402a25113000200d800015004101e1441006800540b20040c43d15011546401e1411100d0201c030a01402160103908900e00311240a8001204894191040d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 850780674 1250 850779424 850779437
    0x4063812240612010c0809060106022e06090f060f0e010b040e1e0403210e030a050d1d0a0219140f0105121614090d030c05031603030605040c020f0d 65
    0x680d00852981d49000c1c443c01019468242d0115615401c403000070b026079103620807140d05070b8a90005a0392001055148000602c1c1702e6095040356031015030401000d5210f1002140d403942e201c41000603103482240072010301e91190810b10001c0741031100000208181d00c6040c2442d4502140084144030700e01440601001080000301000c5100a260b40703481343d01503260143c2e290070304008000015001110380905070142004e0103050a50203588024100d0300d001d940303041d1180d5001c1e9503561080c0c101109a07621080650078481c0a0240a00c41083d6074029002c0000130f1710403c03019285207552014800d124207030511035603411b140022564201035501465031041140161114029110303089081c900800400154454000445242480d0f540ba00b00d007a07c400400e24029001d0301d0342d000d80143c0d4030f070100004070380f0407443e05903994010030036a443c095548048010806091100b034000c2a200c1d0410051802d05100e09070750710840b0b00c0034000700a5494a603d0301c8080d0680183c0c10441d1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 850781924 1250 850780674 850780681
    0x3060e160b12040227010303030c0201020a02060a1d0f1020030601181707080c060c061b1902010213050d030c060b0609040204060201050a060e040203060406381224 72
    0x58001c0c0c00c803171028007020105022a0000080d010384042408100c0010782842500b01031b1f06e0050081c0d42600c000c179005010503030780d64543e41000700001ca040760424800c08200540001050106e1024600041d010f05943c205021008068400142120048617580f60398400401102c0c07040d26044082441c4c440306c0517800400040b24511342d50840148070a003134807072401d00c0b0b40000f9150202c03115041520b81c40d4100c0c404000c5507009040b1415519088100091a800b040000701c12062042650786810300b40410320002440f5680503203880503031f50001c2c2010200d06865484401001c084840c00400c0d0107a40c2c00821071040c2c0303d00182a01c2d100c0c1800103031aa14001910000840680110b41300d03941c400009000c3c2005a80744200b1a00e000760214584aa907950540b01e81d8019005020b1915251b540100030001d5117402d80c880b2100c60540a105900e40c980c11810003610201c080c9080700c00070070410070a01d910760340c144a910101c01ca810507a61b6031a82c3c44094040f07c483d050554 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 850783174 1250 850781924 850781929
    0x101e180b0a0c0309081603140f04030f05030f04060906120c09061803021003061701021204030f050403120504030203061f06030e120f0717091806180103060e160b120402 74
    0x2003082c074024901743c0041030140b4400b10000404105900a035581308031002c624004030741921880c0304c80344502e44100014408121640403001c0214070560440741340c04960f5034183c0c5c40d07400c503420680000b68029010030020381d00c40026441d46440070700401140b04202c90182031003001d0b200e44004d0000850304c101c8102c00c500d406400440d0082c02200c0c0e01c1d0f02d000801002041d0a008024614005d89040b03050420148203441c4817005807082e0503002d031502d032019a030340c00c5125208410017008000c00b0000aa0001c0240320061240e290241c4403030031b5104141c1810390041c888681c600700014000d0761061500d803c0c80444456090010302e035021101081c1c24000b0a605814405400140100c1100d40c0403008003041e902134485401c10540350100c842c018411400242d51000038146034a410090203440980c000c4130003080b156080000d094005800302c0240e1007554201c0d600c1440e41030070714041c0b00c0a205100040b00611215003010300c0707240d46006007560b80c0c10100c1000d00140454 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 850784424 1250 850783174 850783181
    0x30c02030309040c05090102101a09061201110306100c020a050f010309080408071410090501081e041401061202090a0c03020408030c0706030b0f010c060c02101e180b0a0c03 76
    0x40b00080c0c404e0202c220300e240c02601580c0408001401807050b100c84444100081c45101e269814030070b405074000078031208000c8100c80241c10160b00241400300c0f05c051000034402d040301519268000b580300d01e0013034100140302c8135840640040c084a201c0100c0143d131810340305019110110303001407a207420040120000d104045006210b280c0024005c600e030031001810348101d40c0085007184038050380000303024050040c004102e001c03035003d1400780010340c0150140c951025280f000c03002c414510351142d6400740e03002d4034261800d5006000c4800e001e4402e004102c0a05000c120441da003400980c041400c1c043d0007001c84507040e0b45d6580c030b248418400d40448005002c0c540841e47ca440a075a0329544616541c800c0d000442d15180e0191120b0800d201b090154803016124070062000a031181c2010302950f4920108600601000c02000d0300b517803103800c8640b040035047c451038600c5090030708222181c8481ca40004944414204000303007144495a03445500084e01084083d0054403d8026 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 850785674 1250 850784424 850784437
    0xa050120250816031d1801061d0406090209010e0301020c070314150c0a030c020c0907032406030605040b0a0825030507241815020703060f05040210110a030c020303 72
    0x115198054202c03e25610011445892940a00d50105c0c5055042004200d0700d07130707048075035410702104010020107008004c49a02501e0041d10f0781c0c03c4072644c0d0006411191550020a401940811755800342e50b130003682a64050b070150001c502d4005651a929511501440000c017424540e00316103501032002c3c000046509514070031680079061100300038005410140041c000246050410649107100180100812801409440c4980c880740c3c4210080e02d1004480c1030303503e032803c08441d104681150084c00802444e500052028205420002a246005036442c4200b013203034014014541d01007175012440d560380501556584800f5031508403c4c2c172075032000c0c0c1140180400020483d06012400070000d411000d01f1146a05c0441e0a5460303c4218140d008207043c540d0050010440e0004105880340403801202c02d840e54940d00d04041d075503140c40c0240f0881c0ca9605000c11410012031144071070300c0328105400b540403080c0b40f5554441e40306c8006420007103900c10850564500303004a410 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 850786924 1250 850785674 850785697
    0x50d060902061b1c0801140414100503070911030a02070f0c0b1b0619020d060e0907080609030a0804020904080409090c0620100f0b030a0501202508 65
    0xf00c840420071007500c1000240b0889005000d0003600c020000a0400c0c1c0030512140c40d03ca40b080c607402d04968880381e03203810a0035604559211103220300a8039280c0c21b00c0c8282ca00145a0784401d0402d03090509100c2c00340d10414100d1f09080b02c50903802d5650041d658018604ca4006858040d1410001c14403012a84003525180c0074000c08104007200e00010590b00790800c1d404c2926070307080b0600e184e8460301218840716031190510020704004294000300310b0603452100c0880d405031146082020414181c40d8142c0c1548070a1003000480c40500c00380f58004120009135051009801c0301420142c0014002807142c0222b80020307042000b0b120075500038010a01c2c04028440c0246030642850807103005100c003180c4e0302402c1205a1818100c0c4031032561b0018054400700c451040040c0103001c10b15560244107440b52514003940e1820440c6c4500301c0d0085001141d190058402c0d811a02606103103082d800c80c08200711000c00d44d544419201c2201203070151001d242c51420419007c0c01401200728 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 850788174 1250 850786924 850786927
    0x30402010e13050402041b020d030b0406080d080609070503060603010b0703020703081b06060306010b07020d0f02031203040c060212160303060302152104052d0105010f06030b030c0109050d06090206 87
    0x4411550303400f0f28803c40c030a4508010305000c80004665a403c4c0641110060340150140d1445600c240c21030301c60100302500110781ca81d2141e20850070908110629400107482030104a0700d0300d0400e01b0780f07030064000c0c2422032460030b14002003125403105000d41100f030b980000e410b07020903100300035400c01581c00c40b80356626502842080d40078140101400c00c103521030303440030883c180b801150841c12926800c8011740f822081d0340c2842540200c81d88140c681114410415002d42c0b000c2c003c3c0f00c14001240e04055480c9443d10f04407010740c08541010342154001e002c40e412440710300040b00c880c01c04c0d103401c0313054248403032a00b1000351003941c00080d0005080020303029014040405801c19541d0410f030300550f00ca00300d507015241d440c00c0340c001e88030390301c44207001401e0300445005031404034440340300c219050081c3d05001d003918400c0c1d20801c1c00b840000070170080d041e814070643d894035000701c0140028440c8a80001c00404d000c3c091148524020f80922003000360991114014581c041d240c41d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 850789424 1250 850788174 850788199
    0x30406080402010f0806030d0c02120a0f030912080301030314280e010203120a0e0703050d0c12050c0d03020c0102041a03090c120a06050c0d0510030c120c0506030402010e 75
    0x200894025a0300301c0c04604001413411203240200d407040d110b084040c0040c42e43c0741d00b04104850700c1e004200240d8001d8a20070924806107014000e04030002c0c05030107892090003081c41e0042840443c0e601c1310800844c01b424840005000034112811079405142c482c0d62000072107032161951140991854100540c20004e02c500c415032840e00c000400c070b54541c3d204592405005a0712485900c1d50741e955040760600240a140b00e40d40640c040c40c0f80070049a12a94403a9282440c1c2110540d85201046903040d1400800c1041031717522540303a520b4900f0034200000403401580d0342c9405041ea50902d178000c83c00c0c10158100351706030f400621f49002a00344030150703d00d440c410f0303038016107900506c1d004a003620781642c10000e405440484540c001069401100e440700c43c01424007800d180b044035802c00035541064154060340e80103002904414070312501c1c0d4900f803003140e0841c0d844403000b0250310010f00046003100030b081c2d044400980b039603980c3c0c2c1c0e02c610040341c0010810140311741c441e103070100701c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 850790674 1250 850789424 850789427
    0x180d080f060414150405090d020604081e0a121b020309010c02120d200c060a0c03140d022106010c06050603030702090108060117010902150a0c0c172a0d080408030406 73
    0x400d01c2013050702e003000780d51aa41c01a42d240e08151465202586c0048003040000303a102e001004020512400c0568002e0703c0c80d901d000c0f65018890900000340c400c94101d95140d0030f4480c07031034030008a03840101c2c1c2d8000001b01944901031307014401d0500c14461420130564481842c01681904203034203a940d038200c4d010b0098505803503803501031640c06c0c214440c03542e000070000d554814010000c1c2094140a80f0410460744080200c100310100191264541c4407400700704090101803d0f8400056103c40c03620301c81614003075440c01600c80428101c400e001c0340717036000110148034940100001c01c0660300c80d0301003440c6200e002002908180b0880000401d5040814418141c3d444a58244090841c04071981d080c1d60127094040d51001404d0700300c0a00b80410002440088010304100310f5424490b1a102084002607001c465805601c0001c2c5208200c2442107901a0500c0c0341300381103e000401c14415001c00c1a05a64040c1c07251201d8481480003070f0303050f24000d01e03850044907501e0f40c84010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 850791924 1250 850790674 850790701
    0x302092e02060f09030306060a0e06030a240506030105040f0608030c031306090506043822120209040201050d0204030507050f09041518050102070b180d080f060414 72
    0x20034010300030100410841c2002c04409030059420500650550303c41c14100710050b40104034013003c2c000a000343c007442d0b80b0303040050752040c10303503060000d45400b106204045074644901c2d50310058400d510140110740c0c55909480c10f41e50240e0b00003480101ca040b0440081880d9000305810344800b00303489c5445400040103200d80c0c81030075405c0c100d1903034882007510101e0850103560380c040020300051000040c0c0b080c060800e205104d6080145441d04911039018410483c11000c0010001410308040410310311a00251007000315290303d103034a0900c04015601c50004000d100d001800c002c10301b560311910a80e4401441500b045544503900c1c9421590f400e0148603e502540c0010054080b52a2100d0f002c2e01c1141c10904d140700c2034401884031001041041c2617800003072100a00c00c0041042440070704040e51281e40214228181070210212144408001300342c1580a200030404056001c0481c58000b5403500d80041541c84040002e4060806140381960101c03114080155440c81000d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 850793174 1250 850791924 850792009
    0x6050901260604030e131404121b050721140105010504110906160804090e06221703041e050303070e01180b03042607060f021306030209 60
    0x24480161054107100840d15201d0455028001c511880408509818002e030642025980300100041558045007200800c0c2c001340c80c10b450081d4070760510040300d030b0000030601c0341c5890070140301d044d01804c2c0e691710f95030003446c050f201d2100c00d103104000c0c503003e000e00c000c00e110303a0018102c100c181928512500074642481005c0c4281e050410102038504c260045514546010340020b1400d00b1006120480303803811f440459600c00100320001e0002190f11420803400040c8024005a040c654000d05d070610703000c2c0300d190307003821184140e400040300c6a8500509a0007440079030748a94803800c21040a8110009418182c00700c0b2140e4401c0200210042d1f1081500e80c0ba0700101300202030045906182c1d0307141d03108001490b000b00788206000b450245a000e0f1260312060354900e145007440700e600e4002d4a0441c00600b000c0b44005c10030005014100e05801101d20440c108803074105280b079510458410102030640c0000d01c4401904e4003a640c0c40c008511025000300007035684499200310059a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 850794424 1250 850793174 850793219
    0xc050306070f02071a16050709020c010207030311030f01061d06042c0115033306020f0109080d020a110a12090e06180c1908100801050f01170106050901 67
    0x39030010a06003211020294010b64040100d0701b01644011280d0790300f01d20702c4056900d441000c43c0041d6000681c0000d00b00f000b0030740b0000d611409140703400b4042c3d861400702c4102d01e40c2d0a00c200074819003038030820350449129107408814031b102000c01c0c3c1c9540750781c45459a0806c10018010602d074041240e1083e40d14105220000c09018240c0804c98456080c0110003680300d21440041003d0310030340041c0d000c040d500020307007207440300300d17901c01880c00c440d540c1c01040038681c90040003051340500c000300303000014200900c03044ea807958526000744604504000400e0f8007103140408a48249241c0d4250001c0350704440c21071f107071410601154007050f504480080d580c1e40020445580b8030701c00601a50b03004e044001002d00103001c0701e0a0b1940100203940c4003006101c07218000d0108102852003300e00e403504000360422a0901001d0081c503001100c180e8100700502024800341010130b811078848840d061070760302c12040c09a01601c180d9100a6103d103d420000c42c45540414004500c1600c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 850795674 1250 850794424 850794433
    0x1c120801030c05010507120e0112022a0609070603051503030c150c04081c03020f07030f1805090609060a0f06030b13140408030c040513020304060c0e0a120c050306070f02 75
    0x850f00115120300c10248000c001c400440440360005010f94a40d507802c10050416001030807140c009841240c00c14203880c000241840e04c4012003e51f81c2990410011801018103150300c0c141200c543d903012544124420155030383c000948080302c001c14040708600c020141e0382d44035001d00c6403075601c0e00c18500f41400c011510f4081008815440216070440c0c18074805420000c0c4034018040009075118542d0003415001c120350404003107510000c280c0316109032107560348100310a00050242005151355120201e031074805000c25a1400382181d44038004440704482c507503030310000c10820503844c3d101141001402c0800300344907030540c2101c0540e140039106031100e89030703844086058561040e607040001003c2400314001c0303a02c1d40700950f800ac0e013206003646082c1d40c480104104000020070200050350100c240000c0080c6401980e202d41131916008030100070282c00540849503500c21031503500d020651060030440209a01801058010143d81e400d151031a809000c60b40304040440c0103004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 850796924 1250 850795674 850795679
    0x50a02061612050c1510081c080604180f030e060a0309110307060e060304030c20011b1e0507050d0b0f0a0204060f0509030f0d09090c050c0c1c120801030c 68
    0x803d1054592400c02d440c000d000360304c010b401481c0740d400040c1c2503803811880020080703640070b410080c074a00510862032103074a076520508010301c001c0000c2c0c425449a8108150700c00c5001802490005003500411803a801c00501c3ca001c2e070b021485040000d030480c0e8042060b00c8041e0b0180e0190810501601d00c1902040301716041640703404490095002082012020f611700b410110041e5a00c44e1190400724400000c81e1205540714040e8003080d003050806040721041d659200c290400d0100400c401407880340031300d940701d450021034042c0010010168030701460a0003420403000000707003006071158004058a040059010904071900d07188540c030440452501d007114801c07107041312507507628078642d40c0c03104c401107969034001000c280c0c0c540700d4580039454029007804100094442038880c0c607141c031328180240045d600104002002c0c4a801d001e0049120000b041003081c20310101c81e9110342c40400c0042c0b031250590381c04041d000f50110007001d001d145c1c101e44641d050b28001c00d82204d80383e6 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 850798174 1250 850796924 850796927
    0x2f0a0306050f090708040c030506150a1d0c090f0a0807060305060316260d030905010f0b13050c0c1002120a0902060d050903090411120702010203010609030f050a02061612 75
    0x10007821042e500f040039480001c516030b108031000354000344610240d5603490b90f680c582d44e00e08032082d03031040c0c885200e001c01074100d4508000c140700203000c13030026109010354a150907448207000520041c0d00400018480f20389a907240f00134031a00100401980009455420b0700b96070301001d00502020038502008603d43d4940098500000c07688034030a1100b0b42d0500f050300107000d118550b03029240759003e0002000b00400c2c001c1a03410034440d503002035042c0c040d003840d609545d15034000071070315842d150381c060858561461156464407e10004a040d0f02c4280300c03009148158144004a405103090f1092083d5498000b410300141d00302045490362110403074041100d015440007036024a0030480038000ea6566004554040103407030039a803c26032814042029180c001000d200c0c0035030b00041c501041050751030101c0e00005c0c00e00c021400d640c100701d409440c400c0d080c04060203480c40c0007001402c0080401c4503001c2c05070b014080580714680340c210003606040c4828100e41003205541c44c0a5000d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 850799424 1250 850798174 850798189
    0x8011401120609110616050705120c240a020a1b060503180c04062d050a120809040609050f0f070206071107050307031a0a050402132f0a030605 63
    0x3204400181820064281d482c40001d00790450125190138180003c0c01d0295210707405070440071007480215051083c24984142000c0c8207420041c4503000b0141e1188081200150f15002c40300c041d228584445814854002c0f03041100054001a55000400700c0225a0226052506501c180510b43c03507455001008510203005004100c00624280300194460204a02264034070356a5416105040c80550100d81a110b06811003071501800d004403078451214454000c1e030a450f00d420400d03510b82408002058a490743c4a00c5015003101036141060008540880c0c90714100140200f11711542c500c1c8000141c4801c0340c050103491445400030714201002c9006130b11804099010305016601c20009885018103e22044201d100b00c003030105c2c1c02c3e1800c10142001d14024030210640e20ba001c8110000210020000022130307043c80103100050300c0351807240205080d0300380085106036020b168402c003000d031103042c0c001e00681020422204a00c2600400240c01c250b501480910340b64801e00001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 850800674 1250 850799424 850799429
    0x8060a020418140a051e07080114040b0d11010203130e070f08091527030d0c020d0e0103020f0c01020d060e060d020f0d020f060d060f1502031209070801060602010608011401 76
    0x441019100140140107541d01c00c9a2000e69412141c0c0c40e19086010031b43c00c0c0c03900721040c00114846400601c00414607400c0e42e440701038200c8046c4000740c020ba000c00d03188040101c0042410381c20322010b0b06035a0003070042d190841016004029603075551f94800700341e51070030785248010a0b105d416103000d903449141a40e119070b0b07c0c400200301d01c600c441001b50030003800410452000800300b03003100b0001015140c80f038000740c1401c021501c54840c00c200000303d4840c00b010409550013612418645038000d88000d002171000d081c0140c80c1d076200300d8840440c0c42002901c62055100045022000c00568480c4042d214031844009495848409001190501c110701a5001030b1100b444451440c15541c13a05640344050f1000982040141c0444c0340740e00000f050035080c64481c8020310244141d22209401031800300e03030760710004040d80c001940764451008034400414100c8002130303110208200c00c0c070082c00404001c0107910780d00c0600078000c107100d0044800650818a1401c0000c415800d034905 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 850801924 1250 850800674 850800701
    0x3060617040201140705030d060503010b1011070e0718060824040608070e19090807020103090203010b03030309030c010b040203010b1b0c1306062d030e0708060a020418 74
    0x12440154882184110006008a04000d915005600107100c0d58020b8500700d4800c6c001552107440104420081e50b101e501300d107000e80e242c950b501843c1d569000e030807003042509040c5031004031b582c5c0a0090406845811040c0100c0158051017811948003a08814000d0b400220072180d40e2a10b4044038209000d80340c4040d07607000b102000c00c7c8085c082c1421a00d1080040c00050100e544880b96070800785c55500c04d41094120404010a6000001e00902d4104070680300700000c81035070791b5a000d103018021010f410141e0303c00540d4210349007580091300052004044944a00d0300d00400c544d00c2d4480030224800e542030610a510a05290080e41d041e070b401448400d00b0079905050b05104036849000103c540d201c0c814445000d03450704244095044011f41c0007051503420031134003a000c408032454031170907000115820540c0c0c03240190b801184c1c00700c920300400c1c0245881c4903136150070002e0b042a03040d80582001d001141c4642e5000f002190010394089850380a010708900c101c512803082d110 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 850803174 1250 850801924 850801937
    0x806120705010f091a07031e17042402090a080114010501030c021002130e0f06010c1b230a0f0e0c0a050c0d0306091d0c0f040e0f01050412030606 64
    0x4550301a0100e4558503c07107180c41c3c1c51055a602c21700304010030b0140f4000010340001070b020107241d44020035a9004400300c3d191007608081d44001040038101d402000c10791110f00c00807404000c1000c0d0034061104400340c11511f0310074400000c2009501800120f4892608a580083c1c600c40c103000d00c10803030f02d5042610449a10784001075002c2c00d060414070046000352414201c05907120b00c080c0160f0072880e1910304280703040005006d04140c02074a0700d05040101c00402106a0b0301c0070040d0701090b0310402d1002c442c0d078408c0004ca00e0303407280e400a000b120380652820a08440f0b42d1a66410504102c8000e40e10596520ba103000400d10390003407c2301c8001d21030028200e1520748000b0480315146140640c5407041c0f0b10340c8a42441a2001c4803c0080d8550800304414207142c001c0315a8130700e65661044520b8020084c5550340c8810442c09402a05d0100c8a49480da40e55804000040101d4058440c1c24004210490080108540458000107402c5500005a10a119200079101a80c440d82d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 850804424 1250 850803174 850803179
    0xa0e091b03060d03170907080d05030f18011e1a04020304200d0b16022104090e01021b07030302011404030813050f120901091a03010509180313030308061207 69
    0x210311070710f01800076010710071010b40194006181c42c0c03140c1d109950020180c0480e5090080b95801c20660100c001d00b0420240b05018802c55603100c000d070005600d481a4100240000c0e2841c050b00c205050b022940a0044e01e1480b885001c3d0003514080c080d80b0400747c50201c02d1000c02040307010544019050f040c03070412005044200c40602c0c10008002494460554038958455444250031a0700007c180000d40e80044525010000c102d116540c44001d00c209440c81d00c803000c540d00892140010003501c1e441c201c050700b5000c0d411920150f1444481c503002d1a8210302c1305940720343c0da1004400562030982900509880300791840d004e2070303055645418580790b0302c80d00f03c0342c0301a03442c06560601450340d1040501d0002c024418445280c03004081d21784402c400050079015043d40950345000e550001c406400c0400f4017201e0549034122502d06040d1101202e0360042407250180341d032948000618440c4403285403503100101c900c25a00c200c141d580300350074000400300181c01c01c901a400140300703 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 850805674 1250 850804424 850804429
    0x120305031305010e10090b0f0103031b17030115120c05040e041a1807060c02060a08180115090b1819020f1201031103070e010e0403050403080a0e091b0306 68
    0x407074510740640300204405020114460504180840803040c0384c0c1d484900404000c41442a140d22200c65514400d1301d61461b1005008a045034615240307081000084000f080088864071003a4543c400c2c0711500c0c0c0da1590382c0328031401c61102c000c1c00070801c102030f250b035840f5007070080416642c12540c806062615100c00c110304048082d00c100c4c0c40c0e103081c10100b007202c0e00200415128060802240240480c025601410103529070841d0302041b44100540d0050303143c40c0e045031620401303482d05113143e5030380b0760f45440802c05040e400e16a079405d15440030110004420102d050b92107240c42002050f42260400a11640307100c0400c40f02c81080000803a0300c0c0b40c4585410384003074034000240c500080744050000c0fa90165000321000c0b0482c0c4014028022002401c1d0280101580100041414508400302115051040b442c003200074100060815201d0317010395004642c410209a19070174034000251204401014850080080b040001c000103141c9010221501480341c646141d40c450005 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 850806924 1250 850805674 850805701
    0x80f0628090206130504060602010903020c0f0f101e091217090a0305010203041e030c11010219110102060619260a0b09060a0603020a0b130803031503010612030503 72
    0x1035585400d65810103a0050f8440d000188511032a1410420702c0c9402d103010403044801d641c2180c0c0031a8541540b080000350001a03090560104461000c1200c0d160300000c0c4000702e40101540d08040e0202d1045a5070350014494614032002140c0038000780314a401c22541411103200d480040f221503140c9002143c030060740c180f444070481200ca454254a030021450000300ea500407101340c0e500004120034001d1203c43c60303188080e10101a2401155510b000b00748000c1c1404c003504041055051801a80c000c0026041003008581241403800b1581440c642d42540030307024a001d4060f40d0b00082f05807410f0003001040d01901303030f801001e850500320a89804800500011580000ca0201c1080480204520034040c0d205402c1c003c01440c1400f0304a0821201504510600d420a0360904c010781c0c8141c10303041920150501c09441d9610440240c140b1309580d40a60024000042400701d03aa010044078008020306030001c4c880310399150302ca400c00890034040580002c00070b10119040c3d031101c10 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 850808174 1250 850806924 850806991
    0x121e1b120705060f0705061311152205031b100f030207050a0629090604020d0f060e15191e0e0f010f0e1603021605011104080f06 57
    0x8440030142c80b480440c4070390f80011000c14298001080040800904001260f44045d0300b50700d21840b280c070382d5100c009804d03035003c007140700b2440600042036044100003980c1c41405035640c0c0800032942e02c1a9031070610b0b0b850140500030300400c000750070021030f0110191408400504010640001d0b000300f11030203240c407000c0c3d4041507000c010500c0822410400c200c10b26006040019030800d50000521000e0322034550386955100c1c0110f0040c640d40d550381c1556102d50148c50250b07845185440f02001411010003130200d140c03500d000852260b0400b00b06d64403c031040550b00c89022a160f040010038184100b210014152450051000a00d01c41c034000e440d403a0700f20150702113070721385078500604001103c50458428064004200070f0b201081404000d04101c03502c00c2d03884c184103121103064034000200d83e00340344e000140d50008a40365200119140d40180081014400c00b034519295035026204a003180d00c10561a01d2210314049038160003000d00d251603004014882281d03001c00002c01c1c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 850809424 1250 850808174 850808209
    0x190c12030b15070503040e070906050a0516080d0e0601080a05033004240b032104080f06011a041511070306050f04060c09230f121e1b 59
    0x800d0b0040380e030104050501688200059610b543c10030500f458440c0c0001d02c3c0208000c10230b0000c0100c036822104441c4074032020700e04507940c0d00444501d00790301e500c4480010f080c04000149a4422001030b0b100740551501c0d42d003a60450b136643c000680e503500c07525601500c0d40c0c00800c0412590b9900002e01c040c11071001c442a001c142d610034404060b00d50444050300e1702c070711107800c08040140d00c0031204910411040c0401580d500f050220b651284c0918503a00b00000303218840072054201c105440040216100310341d00c44200e590110f898090a01ca000e0709011200d45902c1645581c00c1940d0583d580c20405414400c07080e175044403041d5601c1034031202401000c0c000f001148140c019a40710301d03010142c01040b03060070b191040403a6a01c00e003680400402d15024456110449100d0f5004484400380c1703003940c1d9900e0005a180050602c0ea258040200002c80c182c08402017486400403a64140b002681181340119035190581c4c0145401c040c0101c124440da02d20b0640d403201c8880c02903 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 850810674 1250 850809424 850809439
    0xc0f010531060b03010507050409060807030c090506030a1403091309050604032105072f0c0f0a0512010518030f0a050318070305070807091a1c0c060302190c12030b 72
    0x3e8042400c460703060740c0d558001580000c080c44000d5240c001d40b4001e140d5200100012841d6480ea400308452034046c0140b0f042c0c4800c0420b1090342c08010b9040c03019007056410440f400c1181c0400d03500d50100141a004a44401e4192403508440c131418070350940090140000d681c403a030b4115240f00c4d4062004517014650300d15050b00403c1441100d125405075215000c0e40da4084200c010401382d0007801031505083e1320344045080b0f101146034251654143d40c00b51058007004006001d08429800c10390f000f0359955002000103205400c041c1c0240c0d503031400b0134400c2d058500c10703030713101d105032506903c01003003c00414100c07500c5407004583c00051202c5107103800c0d020302070007428201d40394000d640c60340c030180c0244003910302031203c100240a960000c120140b50180c0d8420306101001e00c5a100e120782110385020700306550188510141d001240713002036600c50710054001d4108030750030043d4050409024038118050f0404c165415009561195170050112040b0007500e0803100b120b410441 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 850811924 1250 850810674 850810691
    0x206130305090d060e0703031707090311010c0b0a0f0b15030403050a0e04020a030e010b100801030b0703090b13051203070e0d0501150303050c01050622020703140c0f01053106 77
    0x44e881440c2032034403e40040c160300f03441c0d81402404440d44503040d4000001407014031a165800c180c408003226807240c80c414140c01484016194500c4005002d0103041d814000c008200025034005c039011100400100081e0101200340100e100e4800c01d00e540100c4100046004640100c0140500e1507440c580b02e802c4860002c00705082c0e80104c03038840702007625a91007402030002030041f0303800c800302a00e0418105d400000e008082c5401840040c1a413098840407842040c483c5c1c00c25207070301d030300191072130007a0030030500d2100b55040014094a160041ca04c034280e110030398404880c0034000950391107001e0355041c01000022044d0000442c0e0303541da0340300200d11040700c00361403100450090701c500c3e031030b81d1a200005080d11001085c0c0761086007844407035000985000c00c0426000030052005031501c42500d4195500b031203442000390a504049100c41c140c41c000542400004243c5001381302075141d409603554210103040700003450b00c0320018641910a1042005605103024840104080d070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 850813174 1250 850811924 850811933
    0x114030903041809060614060a1215063605011b0215090127030f110319050f010e120f090612040b16020307020f040e0f1c0206130305090d 61
    0x3c081055001416250180d0b801440401d102d850001d0140700c00c041c4004a16000056107807040080180034400c01c0384d0b8400c1c03014580e51040e28000451240c0c1070003952030302c002411020030ba0a104580250320240c15200364440c84280744103510000240c81d04904000054507410105503813002d0840001d02c0407809a51400c51070310303541070b112280964802084000414000c400403c00707030302d4454410fa100f00c1c048005460801c89800403202c41c4424402d14001601e590007048c200d42c9849541180718800028240c0c0900c990311410440d884d48140500c418286d900c007840314605038000011070100340504100030b1072000002e42d00e81d86001541e500180e500d0700904282c06000c406441000100003c0341501a080740e62910081c555245040380255288181d110080c0a070000341241c5495031900c1d040241801c2800003920b2066800c01d05681e511a4000b1a5030310450264800c0c40440b030004c1070141c01030f2440954480c120005d600c2c26202640240c01d26500403103610064001714 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 850814424 1250 850813174 850813199
    0x60c050d1103130b03150a0305100b12010203041518030905060a0c05070906030614090303071805032406010905011722050c0a06260c0f0c1e0c011403090304 69
    0x20103403001640e0f140d0824081b80038035001c15010542c01b40b0004442031010a000080900d0308140c0c1005c042100d80700040400c020010480180703d0540c0044180010000011061100d000c031085080000702031221310344d15428018003000d00820180802401941004002005201c0f99400c06d641601460754030307540340c07407415805050440d41d518020f00030084140241c11111121860610310b5040c40740c20302c1d88a205c06840e4405001003400811403002e071030300c891401040300600b9982181c55203001c0c00c11100c5044400280120303d100001c0066000710004000d44106075a41c1c0100151b070b820290500c00060100d5001c2481044034400500c034041c1e0b01880f07a485030b00981000d003601d0083c0416920181c115200740140004480300c00d4000c030070510104881c0c040600381d0350301d07000074109051040380070072800072000141c102c6170b8400001d8002c1209a01041030030b07201603030409641c0c032810f0090045002840241218802170040b9018513080320742c1a0580e4a0300703541f084d00e902c4c003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 850815674 1250 850814424 850814429
    0x90c0f040320031f0213210303060519030b10030b1003060f060e040602090d0b070c020315060306180f032106190605070606030c0909020a060c050d110313 68
    0x6030040c074a42e01480400c0303184403603601c08081c2c008002d41074075800c042c80c1c1050142501440103602146203018104500c54a0000381411446001c006a90755411650518040015400700b0305000c0005614141001880000202c00b014840840e0440c0e8400280400c06401e0007056491400003002140013090128090403c0420704140e5a01d1403804400355503103e25100e5040d0300d400d0042094244a00c4080d50182d802400181d8480e02580041c42e20704032104043c1002081c0b204103e980da030440383c0005006c0c0210100c554843e03c0c0107611003401000c0f981e403609a040382020500541481208c0d400355503418065401007040350203814615009a1945003000389002c5124008446400000d40c0111040d03605442803001d1000440589201384101d6013000000a060300c244100c42d071100c4040c5078040d407000e92841d59010400090b00d17940e034041c1e214283e0488002107441c001c16280d84075503446000781100b15030b8000241c40e8843e0b42c006100040c001000402200841119807001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 850816924 1250 850815674 850815683
    0x504151707030b01080f010501170702011b02060108010f3c111b0a020906011110020d090201020706021501030f02010909020d06080c0307030215030a0902030304080d02060c18090c0f0403 82
    0x1903c40103040014200e660141503880c400c40b0060040c08070b0b0740e01c2401d60741601e40c4075030704582a86482008a00500303e03101e161058000b038400c45403006501160b0241200d410f60b000f81b0011014920301c804941c052803444c10301020002088182e041c50241c13440c003003128041200000e20882150b0010344840000c0000350f59400074076402d9614450112020713914800004005452140d4046020180c019115a04ec4070400c0a0319003142c2c0100041d0f00305601031441503444200c40c0300300c140030f0241c81c071049000d8000d1503004078030284006494010b20031841a0f001d040d0346140c54002010b0a03d55007a810440c082d90049048440ca000505500e841000009566880c0c16440d03400c00d40301d610018429000b842040000d41d8070044c121000d101040c3d94541c0ea03403034204480c03004000b0709000940502010400042c1e8910128410003042d1094098800301d54500306c030702c00148074024400a20084001411515041c41c00c22140d1007625030b800e9500d010702080500160780c01a41c41101c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 850818174 1250 850816924 850816931
    0x4120b0f01090504050c0d0c0807080f010c0503160c0503090a0b0c10024b0d0b01030507090b090112061202011215121109010f0e0601020a0201050415170703 69
    0xc0924141256401000001c80820050500b6620f07161242c0c07001c0304461043e014105002e080c41400b0325900020950b010480302003603a584c04d001e8640721409000c0200c0e52034001340c0186240610206c900c40c00a490104144129071722080ea000000c5c07400036a0103210510040e44980c4030b8003000005410305008480d11500c001e0301603890102c6004d03400100b00d0061091904ca001107040d100b11488044e0040510072881401581c602c110f00b0700d4181021103104a0400a032200030000c0142c034072400c40605c0784024a83c019800c0c0c440a40d40540001c90085041000c0306044003e840350941c1458590b07a06000c0c0c0b814030064403041d801604c1d0144410401004540e081001e48005201015060110030285200800d0b4112903200c1c0c00c094505034415002003200c0d5200c94107040310020308200055840740042240f444190246c442c418145601080c8590300004602074559816921289400d003860f001c81003000304c00c4450700a1154821107a440d07041e101c44d9040c0316100980c0e000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 850819424 1250 850818174 850818181
    0x30504091e0e01060501050307051606050f0403080709050108060d0633090522050f0a0c0e0708040b04060c02072c2203031a1206070e060a05180604120b 67
    0xc41c11039120690214541e03160280800c0980d8106003600d034009003500340a919600101c044086540c20400000c0810781381c030040000078580285031501460003907490700c2803560781c240180c4243d0703250f0180b00d000c22650000145649021540601068825840400c0c200c5104c41d0f01c0904102c1000042c034600c8801019600ca0340c04040031000a040211091106083c88010b29801d81e00383c1030724201c0100c0381d00000082c00020003441c51152515011034001450303604200c1486615400341c1c500140010000c00c44062180c08214000c98010803090499140c40d81e90b130000340303804080d001c10b501400000003044010745000624026907604540b001c08024210341240c07140051090b6841d024080428010b04180c0806488031981404d00250a055004074204107031042181c0c20351082a45004084240020840318015145c580314521044c14890801c186400ac0810103c00200103014010368840c034485078803031000001d03004c9841d15446450540c031498071060140c0d0071444010a0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 850820674 1250 850819424 850819481
    0xa062303010c020c090a0b06040f0608041211030d09020321030a06050a0308041401181e06080601021b1f20010207020d0602090111010204290306090105090403050409 73
    0x40030402c01c800e1018107604900c3d40c00003981c00b0000703070107103c1307483d59403600f400b8540781c4c0300c04c450103080c041204a56541e95810004c20000d41184c2c00c40d0320b1000c5a00407064036000301c0c590f0f8091030383c01e03020b1030401d0194401000205004034080e40d1505c290480f9070104110046514011030101482698915060384101d043c5c40d919440f00c3d005030b607516804c2010580c08015203095410038080c02c0c108151450040795030305082d450003803440724070040010b0401105103212102842e10940c030300d0241c3c0e560409980100c0111901405a00710303881005100c400009554070300c450040c28868545603003035040d1000c111009044022480705010f2003c68200011500c010b005c1e0f140081d850f000155003ca42036200040c0c00400250300860f06c0d140b41d0f80101070b18544180c003000210b441e240d5803c51b101002884596010030074840904401115031034030b00f00c81c401d01c0094001081a4604802e010040b01d00078010707001c000c014080030400000c2d030300980c4c030380e45104a00300050540b401c00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 850821924 1250 850820674 850820681
    0x2091c06060509160215250e03030d1407020c0a1401090e0403020c03060f01060f030c02100c0302030717060a0311030f07030f0210051306030b0102030702030105010801020406080f1e0a06230301 85
    0x1590034510b40306c201048002c2c1206a540c1c00c40500c50409505005940301c0c003550041400948a81c0c1030002041c04150120203a001d180a07031120040c88030161a042070a985070943c0401480d013104c000c04081c84880106404644400c40c1803504c6c6207a180e0750700c2d200462403800c2e10210300680250b48880b5480c501040344035040781c00e80e4218101949400000f501e00c07401005070340103050700d400e406504a8001c0c444184000d150760418007019403184c0d03000300294022240c40010410102810301c0000e03410009502ca100090442a02c0318115140c3c03010408180c051198544103034100c103450404203120072002144150311468500100b4030402948120108480d010040309100c1140f48003101d1f041e420441d9464180000d8203007134007004034158800c2150203909582084000504841c056005000301c0d5000e90722200e09840c0c00d5040185c0060079a01c803401c013260702e00c012a0380d00e0403103a080c1d000412550001402580c0340c0020510703490028404e00514101008a11907040070300 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 850823174 1250 850821924 850821943
    0x609020301060f0803030a0c140a09030b09010905031e040b040e0109050106050306030604110307260c15190905130c170115050d200a0e0402091c060605091602 70
    0x1d040f041101d0405100035544c0c04000e103441c2c1c226441e908000c0e8414003404805c241025405103965640d848944060a142006d210031501c0d804004006442ca020600c61254941c0e8440080c515180c8014402074407240c60115001110900b0040042c00002c41c20007407000344400d240e207500562410483c1d0003101d00591103981801010010400345030f4010901d1544990f000040160060290003c40d00c0d04c100c0e0f801824269000d5100318024600c02c2c807005031800d056030110b80b0703126214005d1015140744802c00804a400038061114021000c0d01c20b91008034582c980f92501a54800028071114001d54500700e0040c0e40e1b0b84410401940034210712851210b1850b15407440d45068103500c04c00d041800f081d0100134001c220306180c0c080341e81040200030001d0406078221600d46801c2200c0380c0c0300001078008103c0d1100e4201442c10a4000e07545d00e45d01c000c0c4480b840c900c40b4144401100d211140440d03145036542d00118235907503402d10040c01489078030407010f00000d0945004c0d18020184 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 850824424 1250 850823174 850823189
    0x31110050702060c01090206130816060f230f0309150603300a09051906051603030905151f0308040510170c07200f0f010912060902030106 61
    0x8800002054012044401e0700d5810395520b80e07982030032401c00d4018820700344000d600134400103100c1100550480003805030b40509003030b900c0d4008000c05110303428149104d103202041c1d501041d1400c6030700032015400040d1407412507224031442010f88061942c00440c48001c400e20101c00d1101c3c0e248200401410b1445880d00070741c25061405c000f80e030341c18103003120030030a143d100380f940050315200310010b080c020703e55001034980344503010143c121240c03409118004c082180501c0124200303008100100c440903100c0d81c0c07501800c5540d102180500c0c0c0702c01d0701415261960440040e5040280548045400c80071b1029828105c04a840500701d03003225014500b6403202c00e0000c20304850840c3d04690013140c0000c00c043d404003081e51046154a20b405035440508100414000c030113009001c494480c0c0325602d03000d4100c3c41280c0d1801c041102258004000442845a50400a141c2024140e05042c102c0a143d5900032a10b01742c3d4415600321500b50700c414400045050034014030000d05143c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 850825674 1250 850824424 850824439
    0x3020d1b030f0812060f012a0c0305060f070f0807140910080702070b0c030f070c0e0c040302090609090a020d02060d330b0703140f0d020703090602120703140d0509070311 75
    0x10000000c2483c00011082c2003d00d003128007540420a008d240211895400746011030400d075281001d035203994003141c01c1280c911450300001c0b40280b19940042d001005a15650141d4444007021a440300c03980e038103000210010440d080842d81c500500d440516181c0e551003107685043c800007800d01240398452120701c41c0601000100002c0801520038a0680d071140988411050a051090083c1035004055413494103040c090f41a060000810a41e07009981052094603210b00b0310203e21012521142540c018401010040c94040c800d40ca04034001010319050000d1303010080d01710703110000c0840c0c3d40010040c07a5005500880c00c0020840c100c01300381e100451070300c202c0075518402c03d00000c04020a603001814850300e0101070780c01d48030070710503510785540c1e021045100035030140350140c0101d008010001003080c40010003203207407071668144500b0809990307020b40700d111349116289019002448000d181441500c0b0340c510035a00480145561403035410003803480c3c1c0c100e04255000303440 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 850826924 1250 850825674 850825699
    0x3082109030307030b10090b1309020a110d08040b0705070f0506100302010e0909061f0b0304200901061d0f03120a140a0206070e04090b0705031f03020d1b030f081206 73
    0x700706641c50220b41440b02c20310394480c0d0780940c0389c8907a0960380190000520118103000c051380d000c004c14440100d41c0c01101e001045040d41034520320720072580102803040070000540c20314800c8010b07081c0107104940c0c0c07a19044050340c0f92814000c040710300e00707008082d420041055691000b50088803c809a44c6082c2c1350508121154540100a02440c4454101e480d0480462103180303201c401002252961901c1c4d081c9480d209560003030b10090800d08c000b10640d504624540a40c6090407540e064507011081d100741004d154101d40b00345045a400801310002c0c0d5203545090010a1446160035482940c6404011010340100149440e242d0002c42c24410352040940018000d608408141080c40800440070001000342000b400020401511030081c08419500100514000c00c0011855400c0e0380308190803005030f141d58400030f5404807100610a01143c5074241203100c1c100254140c000254807a1601500316040c1e010443d0700c0000015810044140103883c190403c40465582d80c4005 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 850828174 1250 850826924 850826927
    0xb010e06071211031b06150609030d1206030f051c0903050a23101a030c0f0609271e19050a0f09061415060403082109030307030b10 58
    0x208040b880605000b621401c50f0803084007041914000c001448203106480b030000c05a0b40c0f1414242c58922120079031500880c010b141c810166241c852018008000e03801c1c80c54001c0b980c20690740c1c69012074a9079480c002c808101940b210b0039084d400307140241004107490860b004034680c4c8003010810007a820f4000d00000304042a00303240d01c0e03040307e00000d48803011401d100464403c90580c0549105901e00e50203424050b4001e000307001c40b0b44450000c25880074040c95110402c0700c1010341c9c4912405440003041c41d040c00602060f0341c000c0c0c0100c0010310341c04000d9421032101d00c0c0c0104c040b130400c0e0811580e00e5040007604030b400c3c0d000340620844d003070038422009451411010b50700c00c644c50b000010706161460740818407051940c1014011403070704c6e040620040c001c074048801c4035031180000076048000501c1c01001b925010305040d1929241d501c5811298001d0320281c103c0018804a98100100340070441d4059020030300a1036607802c04102c09000c6800b0141c48a010701c0c0c0e10591812030302d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 850829424 1250 850828174 850828193
    0x26150301240923071205010303020a050706090b0a14070503043033060b0d1104080c010c060608060f162d1403091f09120f051b010b010e0607 62
    0x2114250180c43d032510380e00744c2a5400041c601510700780c546407000000c00d155001840e4034a0760301079010349a9040c2c03034801c00c949090080c020002c244d0010400741034207502c2125185050113000d100c0c075040c01c460b60f40d901e08540c49503001c2d8480d50301c004110004141c5010346180c00890306403010382014413641d0f80a400700b42e00100345010440080c2c0c4003c1c5048180c044e05030070f080f207c9003004900c0d15041d0501203604a05c21400c02c0610386100f030815141c0b4041128140c0320941e00030164415060011642060081c004591054544900241d4140c040007840d004400b842c07120f030301501d03118119200400d01d14101004109401d4004a8600e070848040200050350b66840070301c1640c404000c0e00c01c0311081140019000f000801c00000f80700c0401c10021085040c4000546003c0b600911026a005030a0140c03d103424444079400280c0184215403003c2d070f0340d04205041a081d80e00001c42000c4241e00e81c04665140c803400c149035a40800603560b0803400311040e50801c141901d41e090003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 850830674 1250 850829424 850829471
    0x7020a0f080306040f0606031a0303090901030b04020109150c02041103060a2d080607030b0d080a0f20010917040b0912030405130608010c261503012409 67
    0x500e00000120f00a40c0703036600800c24002801200b071020540e5050001e0003040c02840004900e13000b82e01038141d034a40441103401124004001d400c0f40c4e42181c40d80700c20141c02410490501c50140d40006107034440740720018840c00380d92101c280aa02c14010b110030707681f24810f004290b0310200100075050b61011042030659411242d514000040d440102c81c8102e02400b103008076102040e00020a10400900d2a01c10005070350103102030b5025009110040c01800d400414440041c0264a00d0900c5224001c955401a14050002201405c14030403520b41c004400c0c42540d46034406102031003440840c10b0144144000c001d8a494903100f201c4d11240144002c00e403282003450000c3c0da4032007041007514003a02000303103c4420496a03100b4400289010321400700194246400f46c80d84c0c41c01489001e4141d030f806640c5106040340c821001610365001080112680d00c0d2110140c05078038244a1003845030f0b06407100c2d203201169904000b80c8110242d205814940c140308032140f00c08002d030b061082 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 850831924 1250 850830674 850830683
    0x70302090c0304030f030e0c0d0b01090f0905150402030709090803180f07090b04060b03011707090204050609091b033904060c0c122924011407050c0907020a0f 70
    0x7c0519100d025a824055440070341c1ea4850032190f554003c3c03000c0c40078064100c80030326004102410409180c8001d0325541c1d070003d0540d80080344c806500c5102c0c0d03503405901500c01801c0e03d400d50780350b0101b001269030111040e50b4503200401004280401c0c080c6214000400100a161810980e005146c0d00c0000f805100492500d405802005c0d4441d600130401070f1400c0303c40c09441c2d6858101482c140f07004617400e0341c4244206c3c80c001034840001c0c8201d50030f40300040e01c0713549030180c0402030040a807005000c0d44641c0450729074050340c030444100035601801c01307144000f40c0720b50460b0412109805d40c0c0100168045c0c01210800504035020480741103a00f6420840c03006401801e04c040300e00b41641c031420401008c2a04401000411004c0c0648180745206038007100c0300200d00200314981c111080c0044000c3c032100d8841a944030b203001c803040b01051414588505105168940940202c0b108440300c1d0721401c0a5029440d00e81a29613114405100500c1c400710540c80381580700603192000341 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 850833174 1250 850831924 850831931
    0xf0c0a05010e0a08062e1503050c0d050106030213080f0d030908040b040f0303030c020102090d0602031503030f030f010e0c0d0203070302160b0402010f1d0f180405070302090c0304030f03 82
    0x8410748441040e24004c0c03920340142ca0443c6050384000b102035140e290592100d035000c4c0940110030000000400503542c429400141c804585441900100f00c003400300c00c8841d006120941d411803840c00742074040e00c4d040e900035031505255a082000d412164204080750b402040451000c50b40c009110310301c0005925000c11134552034282001944500c0d0410050640c00040100b0000da80d4040740c000c0300d120360380400200040030780c00c070300700d00034196407983c08880100c0c50000700c4c0258024542107080e480400d80f80c2d4181500007440c42c1d0102c0c014003640c400101c208040481c0b04008140100301c3c4c1507000f01949070100c0c0b00d0003144600001e8a1011380d010000c60002c510980c140c980c2c20500f020a01d4001202c0d080244181d04200c60890018445a40707100701540310b080d018a00d0b1a1541e00c1d80851002d01c0d003000340c80141e5108040d04802d031440c11055041a10501c203010340c0c000e101a180a5081d401404031001c401400e5040c417842c10030034880001e501c05402c0d64030041d1482c000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 850834424 1250 850833174 850833197
    0x5330307180611210a110c0303120411030f06040b041a01090504060f021804020708070f080a020d030b0f0906030703052e090206041a0c0313080f0c0a0501 68
    0x1641c0d0304041400500400c4000a000700704642c00100c0034041d000b0b1001221010306003120202c2e0840c600b01070b02a24502d050004000460059001c54041c10745641607942c00c418041c0440d1941e0440b410b2115010404402c2c0400c1c014030b101a9400c4035405d030050302c0c0d0102d41110080d0b4810016000501c92443c1c5d10014042c408182042003604050105180e41565034281b50000f07040c013500c0995045251510070416a117040c03003161520310310b90042503c01941c01c4100030003504010000d41e005601084030700001038081481c006201c0c03190052a44500c60124000e203400d102e0415241854036022180500e0b5075184519082c0100440d1104031039031765035011a007007082c1648010410301c40c0105d55401c043c0d2266502c8041008042042d0031a00480185416295403600c040d4111b2400c00007800344141e110f0303000a10300d80d5104032500e41a4401922440e41d80550300316003020030b0540302440008018085a0700182c14680108030103240c01c0e0004010302e03400e04c0703114107120681580 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 850835674 1250 850834424 850834427
    0x10050f0705100207061b0807050a02030c070303090f0801020a0905100c050a0507050102150f04060b030a1217060414010509072c0a060207061b020a030503031005330307 74
    0xc9440c09980441070342c8000c0721540c0044080e401a0408170303002400e00010001804070040251304a8469135140c500c0c0741c640300c5003524950320241baa84c0440c00304010300a10300008012181c011440380c1c3d1400d90081c0784c8510615041c00030b030403454440e4010031011400c181d104e05020143c4001f04c3d501c2007041502c04040d00c040f444038600038018014002102e092160100f00b600c222903007078003074a6011900d5251608941d2080b00c0107006003580a001c1000b16040394005210a040942110a02c50315074444034042c174080d0b48035900150300305803801c10101c003080c02c80f50083c1050b41c050100c028101070f009010031b8140112400341a03404001800780d8410b10a0601040461404c15040c6103686070301800d00c000c0350211801754059400000c0c03100e00c0040d0b100300b114203e82d115105000c08860022100c01855000d07a441800042c010001c10b0003400214020b00032911010301142c58041444200140ca8041c641f0b0312050b940d851031641e850b00d1024581c4040302120690340e6568200 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 850836924 1250 850835674 850835677
    0x12010312050c15010e01120b0f09010b1305090d05090d0b0a020f0d02040806011401080f10053d020c2e0507061803170907090218190510050f 62
    0x2080e88080c800d200f080484812000740d2103050703500328000390f00180c1e220740200344004a01c3c00c005000503a114005985584042c25880e000280c5e800040340d04040c10f0005554040c1c0c0c2c03440c4100056448040c003250240802c1000049181c43c2000f505100d01800007074410000c440c0058098009200000c5880c1e1081c2c0c100d030b146e1034090300100e444240e582110700c0250004c5c060710000b48510b400218240040160000000c40e05a58103840740c2e9072800100d4000c140034000010700260380502140e1039444d200c4516840340650b05070750b146040300031500b0881484006200440b219003840b40811070340407440020008040d513400c0c1c1e5856005a11035502140340c040c605442115044003c0c84c16400402130100c1c902800051203e1b01481d00710044868503080000c0104048103020300d10402d41821859110150405603882181e44500b401c0030f030b0f40311070480c00300700c07061145c04181803800c02c8480d404d11800150441d0b02e942880041105010f030004003030705029001c510900e4441e480340 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 850838174 1250 850836924 850836937
    0x901051909020c100630080712121b14090109030606090509070603110301090b0d0507080f0d21022d090108091515030106080a050a020a0b1201031205 66
    0x8404542d19000c0d00c0c6440d0301c582c3d02c400f030303403242e6824000009950a2518826900e2040c0010080b02000450000c0003080c0400781c0103d1f80e200042c01818049240000e01040039002a10703140316040d40d07108000c003110340c80190801585644d0208141203980400340000e10800c3c0a409a5582c40840050300c66401da64401043c9504180002c00da00700c1c90742200d030096209a00f00c0701b83c40d80b01d140680c203071030070982c411140075014001044040d945810074446228040e002251145107030300e9141c100701c1d00c0d4000000d0350b03218200c24100000100903a842100e003500d031406542224a0790400d1102d030040d103054200390013051800b40304410710400d6000640f0201d0383c0714003401d400848495070700304607a1140441c1c5154005a2541c03808110340280d45000c10a0590a540d019045000064051503068040d0760f12103001c20030420401003680c00c01c4c0240000d24039a0118410041818015042080420014440c00d504d41c9a41c0b042141504d0b03000303264a0fa1b101560780101c80600504 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 850839424 1250 850838174 850838189
    0x20403140607021e1e0f0c060c0a020402090d020904060501050f060901120e1606020c13060608060405150a03030306140402040303090314100c0804140f100b0a08010e0f1b09010519 79
    0x2071710304503140c00005060302240045019035251111400c100700343c41c041c010420840d034101c040700c84014541580108600b100080411002c118a0740100300004d00c12a01204e11540e42d030010300c42440e200e2480444642c04555081c40d100481000038214220515007100903625401c6610402c2800d000744901d600c5995081070080e42c0c2c03484d0096850340d01450090090346854540c0402d0b51250060405031401c540b00c0f0707100c0e92288010700005000003042c140210a80140380c00040d569280b03100000c500980d000720b50306003840001d0320b2100c001d4025a10440c810041000000e800a040c4000c983e04107004ca103031405802550b41c00c00121060310a4624603102d4a5142c154001076094015409401d50480404401c030340142d5484908800e85e00c29440350120001404064100506241010302810700340c540c0d40441c1c0c0d09640f41c1c0b001c003401035080303030b0700b4400e06010400c4440d11030305041c01011150184070002c1a100d002c11b02400d4021002010045042e1a040780c80f2002403008 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 850840674 1250 850839424 850839463
    0x7060e070b1c050601080412050c100e0d02010b0901030f02130902100c12080c0313020402040b0d1e0612030f02010b0d12170c040603021308060a020403140607021e 72
    0x1a040900340b4000700414400b405894a00414959403150103d1403040380d010603200444400124291070070382181d040c054a5115145880100c80070764020220b07129844c0005201402983d0000781c01d407046546018000c20f00d41004001240f06065002a0103030107455045d44004881190000383c41013010194004c0404a0550040c0e54404120407070b450040c1c1c2c40b800d00c0d0103480c108880308002036400142104082c00403d001c4058003014603099071001f00010325096590908030b00980004038100344040c1e0b103620300300200071801c110345035170b6041c2041045401d09162001c03820114204000c1c0c200641d05002c0541c10f4001d40c0668090000103061080700b0480d03283c140c080c0d425104000000030b0881c0d00b4120310104007800c25000e10740c0007064508090a04030210000d41000c80341c0c4112005160000880e22000e115290045080c140c002da901d41c25414503e0600b0006049054250700020400079041e5000c00e800444e4807418148110b02c0c009450587e00e0b01c12031841c115480f104 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 850841924 1250 850840674 850840687
    0x20408072103091a0706061805010506040308040b18030f010b010f030212040b041704080307050c0d05030313080d0e0f07080109150504060f0912032007060e070b 71
    0x50000e40351046400c0032500301c1210110310518a0003080c41580100070030010b0100740071070403000d5140b15000c2d0301c40355542e00342211a2a000e050f40d403694480e2890b50280103802003246858020b41380900416903140c1c0c9001e1075650b401c002c500c114401e480b110180419940c910880440c800c8030307100710003001c550211b03058200d103c0c001c0101041e1a4007040c2c01c0340c15000c40a00900a55903001c849001400c400c7d51107445081182c072004008580341d20070502101072a00e2100041c0002c3c00304000216100c14040c600746240c886903100071481050442c51a40010304000100c9600c0400704040030481d00300b900d0225014090001030314007050a1450018004000180d0a120082080111074140b542c41d80724034200d6012410241c40e0407049051a5000e03001c98000c0340c1c01522030f0400040f159540f5080030229030202170304a440020601c0ca80345000e505006040c0112540896108880110491400c0511480d080203202c1e9417904e29505400780c0c1400071500a0101a01903a030300d41 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 850843174 1250 850841924 850841939
    0x603120e030c01030b1305060432070503101401030b03070b1e1809070c0f030801060f09080d0c0c0e010e011d0601122d1e09050d03020f0d0204 63
    0x69008505502922603502001055131080c05691503501001d4011145a0310b51081100540401005d642d00151203c1c15203e6400041140c003d50301070701c000f404100c41c140ca20701d100110300a09042c04100e000e100384020700d40c4c000300c07040403502c4036900c000d2006220740060300a0000340705c00380d905004550000540080d1070005100074403580c0c4039400d05000b2032101d0109030180400d200c81c6103c283c0b1110200e418814030080c0c004069050801d8642d596580d00c11407070010360001c500141124004104d0b8941140e000b60034541c15040001c003482c01c000740590b0b1810200030328010003d800c0c2341d890038455171154200290100079044400e079a1184101c07003080700d0a105d03403483c0745c2c184000000c400d0980e030001d0780a00340c140c0d50041d8481c0d041860f507010b0541882e00c500c1c03480900d5140c1601c40241006004181603290011507218042a032006040c210302c07114101060524504400042011401020030012402d006858140c54419445580914a43c00640750b200050101c1d010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 850844424 1250 850843174 850843187
    0x507020d0c0b13300905121903090f09020403020f0d03020a080f04090e031305060c2e05091e0a0807020402031803071406070f050313020609032d03190f0201060312 72
    0x100c104e0f07104d24074144c3e6100c05100f0052a00d6400e160360383c001d0818040224064104007450b50301030320304100d48a0300d40c2c00d078030b03110b131501c0c0d2104410039400181041141084048c1030300c916022502d0403c0c001542d28065110422144020720352000000e841c980d48140c401070381d02a0038440710400107000c02c0a03000759654462940004004000c450000d8140303028021180803c01100181c0000b020803103943c0200e0600d1514409045140010a480c410b401e10543c0d1240b02040003c00304404100607511540080100c0c001964001e14144408650030304c1c200d03207a01e64107540069072680d4000d1001c100030380d400301030300d8280800100201400148440754494010032015107113181c03a1840c05540f4001810000d8021450030b000094000f241e802c0040c10f030a0004c0e000341d20300440040020708122054692509103100328034054071000c0921032006101c08841e00075440c01286901040e1049488052a41040129140c044c080352003034100100850b40590301481146400101420a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 850845674 1250 850844424 850844513
    0x31014041104022803060e0f07092102090402040b0901032108010f0b0c070308030c120906060603180a0816060b0306060f060f090904060507020d0c0b13 67
    0x20342031040c80859145064421202002400c4c6000c0d030201d40c074081c40d034900d40601000e68060558800c00069003020000c18113100740d6950105040c030380b5000401030320910403900036030718021031100041c0d03540b04100307402c0c3e4002c0c0c0c0403100c1000e1581d491002501404402c41c02e2604502c031480000200f190140f00d15007942e8007500441d213031504030311007241c40140c244109035054565400810100d201d030342c024040e010340c03031007030b40e410070f4403501c0c0c800c0d0652042da207400d001c403000120031680345100000c13560440d000f40054a2642011000601240800340c18010600346242c1e07408031420b0200b22841c6000d920411031505c421b0b210407588094810b821003541e11a0408003800c03168500410310910070280201016000900b8000307101581c3c01c800240c0102540070040001d06076111610688124454000402c8902e000540242403500380c8841b0010b10a178038981100007400740c230049502041201182880c00e419040504c032061031100b203014280e001c0814400c8414070030074054003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 850846924 1250 850845674 850845683
    0x30902061b0d020d02030901090b0c01020712081807030c030212032106012703060203090c060706020d2003150105040506120a052d1005120105040201031a030a060b03101404 76
    0x901320b1070084e41c0b24854042e401d8001044e00d54140020135070714020f80860f5070040001400e0071125501c4429450204a038030000c44c41d140100b0107002e050240c80d810501941029201d85440c582c0c070030011041c80d020080c400c020558050900c41030030410ba91032002c0e20040280300ca03507941919080c0c004152030071800665040304000c890300400303c001e00d10902c1011080f1085281d51620802034101174a11015809544400345055403164090a0102d0103400700607903c2d41c02d940c1c9031080314402404550070642c0380349440021070602d01502c1d402040000d00749464842000100e405111303d400ca6903020034080307200004400d00c1042c003807140001600802142d00e80100503079891418807907070b0b461481100d400c80310f03000003520f1894208142c0024100320580b50400240c00070000d80b550559a03544004001c199a8503000b80002c001010400c90140e40c1e00c500442c0d110001e025014103400e403140104060b98404100303203a034000500d01d082100ca10910890311584030140c13000ea4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 850848174 1250 850846924 850846933
    0x304060515040603080319200316030605220b0409060b0415080d0e041d0a030215160c0f021c17090901060c0c0e0403030623060307030902061b0d02 65
    0x74981050701c941001e0301d42048074181503940d600c60025908070741d1001d030040c850b1210643d0314060441c0c159030b145641d04080c1c40b9103d281030010842c81070014004039003010f0511404114580b50506181c031114412440b480c1840961990400030b0300f40b21850503037081c075040d5010140f080700c6e44844039543c0100c40501003c61180040084aa840d00407040f41e508551282000a4007422000312007035409040803420f81e03101c0c0500010031100400d60030041e0010079103201007650500411070700610f00d82a01c4401e0a08051000071804121200742c1403001c1e00c1d5492080c81080c00324030f5100ea900400d4005140d4003654810300810307003820101c0f45a40e1600440080c4080f00e400e580c82d024010741101c80c4e6a1900d0343c215070342c00c007000050340e00e505058000700d0070454040d040b40c825800798a020911501e40100c5882141c220b0b110900c80b0310000001c102d4030b999240c100ca0b0441028600440c4660650000030503030302c100c0d0301c01e0300107030f0051b1000740c0421404565500d1807180d6030242d5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 850849424 1250 850848174 850848211
    0x30f0f1e0c030f1701090b040b040207050312010906060806150c122d12071b0b060a15080109020309070b0c0105090d08040c0308072301050906070228031403040605 72
    0x361040c900501c0352850310324640d401480080d4991f4003c226101b00184003084604035030703000c1012603020703003410b030744980000442900f40090054000d00608a0400c00c1203030a103410b40061122101030081031003024250724000d03041c0200415a00d03d84400400c0e102d5000401c03958241e03540c8a80c000c0c2d00c0301000c150154001440314207200c80b0901c2d2500070580f50000b441c8040701c1440c0020900802d00015040381d0407440b000c511034106042c4940b020322182d0504200f00800d4124585c82100d080d41c8a10711411041e034042c6046045945498002d40c50303407100e4408500b409019000060410b0011a8981c0e1640c81508410b019001001c2170392a80c040c3d00303c0c221812a4126005808000d0202c000c10002d0314001c0104605c030f000b0000d0750900e80c07040b01d004406401840b003442880c0e455030140201c5a1007030002d590844001c0c0000c10113400030b132511001c4942d1111405022340984002d078003e242c0500880080d401035181095920324180c41d0500c000c02042d00c520008a050326520b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 850850674 1250 850849424 850849427
    0x1206041b1e05040806010b09280f0b0702030a3302040e0c03091e160e0907050f0a0e1801050403090e01080309130f0608070909050c0301020403030f0f1e0c030f 70
    0x31102504c1548014002c203030300380801d00650b540146a40c0341c0181120000b403007110806240c6074221321922800c8140c0b2880c0c40e0b6048040711a42d000030624003810011340d0010f035000101810a07640c800a45031510148600d4540002c001e005448500d860b0709000340100215640144140c50007041101e40e40e0b19684e186c4402800205c9442849034051b0194064070031a0b103a00c003042048a1048502e5400080a162143c1d51a44c1c05502c400140900344040c0720018010b00014180035290106440c0712180000c040c0b03012481814400c000b0b000110b40d16071100244088103400c0346d0001d1001381403a240082c1000014407c05955a480340000301e0001c80c080112500d03090018a024005041c98440200a00114401c1d004850361010000f0b8146070034800d080090014050014052119081c0203040c140c40d18030b01d074441d0340704200034000290012a10707140541107190480001c0135048041d2030541540200c2c600419005588000d020350001d101110240b10340d4450040c841d10307010 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 850851924 1250 850850674 850850677
    0x230c0a090e210904062301020109020604170114070206040c0803030606190c05011e0b06031003082a1c08040c052704111809031206041b1e05 62
    0x811210741010010480c4480c4502c682501c140802400b075150080b1080018204c0d46964850b4030804401c09480000d15945401041c26000070b000902c92500c8507800250103108074050500f010707030381505a00350280c007544814030f64012089001e4031814450400b80da1024202e40494050740c40f51400300f0305000100503240681b0028185509080b001106c00540c02404803c060400a50140400110340240280c0d00104052250703500407079141002482034559007000d50b809101c0400902c07034400440c5440300c04880d00310760001e803200d410041c0605004900115200b06060304e0a031021985c80c0440d42002001000303000c40d80c0c04070340030300030354500204513006469204099010011400c202032480c2d14030703110b590100440d600c0d009810100720b03801c0d10144c0d072520105e40703900350341d081550301010444030076006445103107000f030012682d070b01c03c44150080504041d00400e40d00d4880d03410808044000005101d1b0f000c2541800401c81d01001000c14074040502d4040980940100d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 850853174 1250 850851924 850851941
    0x1020708190f0c110d021908011d0a0b040203010209090108010605130c0c121b0302061008122209060824011505030606071a09010609150e04230c0a09 66
    0x122211100d1843c2d442c0c2e00d00c00c00040d80107942003585002404010703900c22950000414407261004055420100e4003421204983c1d211600e01aa524108003118400a80c0e64a103952119109541d0742c0c447c408240a40101c0740025044911440007040248042d0400300076600d0035034100b400c014224000c0700c01d4501e01c2c880e034408078102032084408074100b00d07540c7e11640e90f0f50805110303410390710022408007680483d060b00160018010301c209101980c140000800200004203c24180e00c000c1c200148100c1d0b10611000700151410303403681920400c0b000c01001481c03020055281d807042099100c281c842082c00c1400800111f44071061800c9600a041c1c4070005442d40012007001810f860340e520203003007594442010310624001a00c030b1300941788168062001003a2030305001101ea0700b904c44603004105040c1c01d02c01411100154242040115004646000c1150700c681c20004251a14100c1d842698039448514088041c00001c0d036110301c2c1d078161000c0e032155556031400e004580100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 850854424 1250 850853174 850853177
    0xb07020304030c0b09010c050f070e0c0a02031c06051c0201021e030307050f090603070c0c0e010b1206010e0306040b1f15030b01110a05061e0f0403120b0301020708190f 74
    0x22000340070349034244e0f0140c141d070310041c1002600d42e0b49945030940b4002100d030307901209a020a80030301045031011040c0ea081444091054140b18502401079100d000e020401d601c005032030359400b40c2c0c5405980002009002c00b800c0c01601e21441e03114094000b05120003a400343c4035004040070020b001d0b801802060000c900a941507496580d801c13103980d4080064a41d01c201d042c0040d02c1165150b400550059030b8607143c8031090803007440c0015041807190301002110b04040c004020343c40c4a0003c0f03803104c0d00e00c1e441e020944c0e43c4090040c2e9591004600c4140c152041c50204410030840c070400f1400303402c0700d4144150365031803900800100c0710180240c048032503001c8411501c8900030f0b0815020070740141001e0780780741c80010066217052241c4d003098400e40d0082c0c046c006103550b043e01c6d03410001002c0c501e010440c54048170000f948a400340c0b0080070041c095100c00741c92901d90744a880000340040080d540e402903810840d403179410000c41380c00c11a045405051400d40521814000720030039 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 850855674 1250 850854424 850854443
    0xf01170a11091005090c0714060705030402100c0b16181a1602180103060c0c020906010c170c10060605090a0b16021225060905041a06070f0b0702030403 67
    0xc1c500340b002c0750201a19100514088450200303107680c0348140d0b144201001d00d038180d200e14160421034148031041705640e0b0290055014841d0301c6504c807040b260304c5601a02c180f1f01003c4036950454400302e4000c40640300e2030710401441200b1071500060482c054082c0d850300c040351144002070301100800d00c41c0e03039215038030b07054401d01c13800034030001d480d40d8441c400905580072015004240201024038004140f564000014010414640328200c0031040c2e070f1030f00b0600400d840d40072a81c0e100f405000305040c4000303442c43c5410441034060042204030202900c5865001c05203040d0390b1113005407180350a20341024808948180b040080e18003060b0300410040a9620f0481444400c3d401851255825003983c0001d2016844051960000701610350003840c49141041141131949500900303008a080ba0960070061075910030074040645100301d40018030040c210002040040c01070f050035070040ea0120701201481035202c4000f184070b00070150741031940d903901030803070300d83c821404010924800b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 850856924 1250 850855674 850855703
    0x9211005090c181504230109150905130c06031406040e0303061e0406060909051e0a0e03251223090613030c08010605060414040b0d0b0f01170a 63
    0x203180754400d13045520015004803980300c400100301034134441d61040450b900c00140540343d1212444055005001891003004017201c40c00c100241c000c0248241c48002c0e840360040744400300c0000500030919404a034044401c1d640c0e00010b0050210a09104820b810090020b03103941000e009011071f14481c50091481d55039032074100481080302c9000000004e820038024495904c5520440000d800782d501c0d00300c80c240ca0080c150040c0ca50003440444140701040d644020031070b01001d0190003012010001c699950b20f061340a2443c05210f00c864152140c0030030140086600782401c03546180643d070f2100001d200360000360782d140000c051784290741d82c0403001662004913030005060100c070300400692a14608040c1907000700803941003591440b0300c455080081080074441c074002484261045400c061800c558140000c40504069028030f80f1408112956035500e501c4800c4954008240d10060a1614100c88604003d000301920100010403c441460000480d820310030703031100951150340c4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 850858174 1250 850856924 850856959
    0xc2a020103091a0705090a05060c0c011b050a11090708070c080a1709011a12150603010b0a0b030411042a0201110d02070519031409211005090c 63
    0x4401441920441a40719408030a1070540343c4540c0030300b42ea070350b0302911007802004020045420341e000782c0c403a06041105c13032245400414032242030102401c02e1340043d81c04001e40c0c0398148488800400354051509500100b00041032180340b4880c0565146405645098090700c101d442034841300040b900501010000540e20001030004c44a07920b8002c200084d5050740342850031081d28103820503511145000c0c03459103042e00c1d40004080c11140483c0740300f42000c06a82720301d12059a17000e0390442400040701620250845003207c2c4001d801806950340c2c6d5802f1340040d0b0429501200c881d1203221400006107080c2c0100309a803943e13160030000800544c0608440c03038003054003840965407120610502030000c00060115000820780259491103149803d904002c0c191080e416010101401e02c3d0100b58000c02c141038140d402c8140558454100001a0300340700035950321107900e128170030f80d80c981c8003000c2001001c000303542405000a89480540c50f48441c842c6a00f2900728001030f00700b03003001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 850859424 1250 850858174 850858181
    0x10b090d0f060219020c131a0607050f0f06150a060e0405060d0506091f02180d0501060b070c08060601020708120a090b070606180207030504060f051209010c2a020103 73
    0x3a205480043c0307005101303101c4c00040f4502d058403001603045000c10003a00d0030320300380d00003072082c80090802840031360485d00300038140d50003809401940e002c5003007410480c04020308003004018500300c0304400106c010303560b03030340b5011102008207410008600e501414202c4000c4141c4a80351140d520040300d0500f44802000c0c02010b0a6000c0c24032003012010902c01d003c082d0052889034080e0001d1041d945034642c0040c0c03001c19010741c084c410012000c004201041884555000300d900044000c50350030068054034081e041442000c07400540041002003698100703049848000956003266180303001a41c480c640343c80b82d041560004030380200310406078002040320488138100011216243c15061100e6080f01c03e08441055841d00d0a0000720000d01780d50044500540c3d00f9841c01c129076600500a0050307120714024826200d408241103402034080d5446c4642c80610140d0615000c044c80d40a044d0440e00c010100303440c94403070201e01840c40369184a04d00a40906240056140e004600a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 850860674 1250 850859424 850859453
    0x70b0610020a1505250201020c0f06010e0105060a0908070b13050102150606030c04211e0f020108040809040f0614060414060c01091a0702060f0601080a0c050f04080106030b010b090d 80
    0x40c170490a642600503d6811580f55805100c0d400161038003880d010b428600040d5580e0711016600c4807004010070440031100c24151402561016111580c4940603a07000d142078104079214024601d000c81c031202054007030015542d041c02c9194043e0b55400042ea1101c2c085000c0f008440e44510024415040c02001580c2140039040031505d01a621030284901c0c02d80381d00504a5400b40140b818140f04125640405040c03003031510307034078880581e41c609200100034074009051042d80c1000409000a003c01d07641c2002c8040c005014012692041400414075401404c2c580581a4944203c9041c25804d8400307480b4580800c07007446400c0420030407240c0000d00f5000c0c141d03407511442800905c090303c0a80615280d0490340e0ba0721308000704080c1c1080c00c0180400f1944550300100040ea0381e100e20050340011540310002031114600c0800c0fa620b1041e0240e40314440350020340010721101c1540034404403401a03020080380d903203a1071141118440c00b100e01e54010700110441000c100c035080010310 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 850861924 1250 850860674 850860691
    0x409030509210f1e0c0d060e0a141c0e0f040e07080a03110f0606130f0905071d011703070201121404060219020c13110906070b0610020a1505 62
    0x1055100c5442482c00345100c101e40f5141c0c000002d000e2055401800c10450302d60003002a2086851a10128002c007228041c068141a1182e40c072001c45102400607111440d0029500c40390034503000d0100f9a00d4020203106c40c5100e1f418200b01d42e44900c14503600c01410802411964005510001c0202804415091003c2d60141207800610f51108011400e00a842034492601c44404440154203180c1c0b0140345d208641c1201007001480e90790f80580d9000b41414410000300e0b5800440b001c4014104900002c10a115291000c921080c1c2c40b0017a040c1c0e4820102c82a0740c1d6a2905134800c00505d5200e1011010341c0140100001580503049001100d94a10000a190342075a49800304a0740141c0c0e068403100c4c2d00048482c0305132403a038000340580d1103030300090586400d00e00c08280e41880c440f905010745951030300c01d0031b009030420007194503140b80104110745a481c541001c0500070b90580341c952290401c42c490074221390000c21558080b68200c030003000e03144000c00c10030002e030500402c03118 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 850863174 1250 850861924 850861969
    0xc091403011103093a080a021204030206060301150803090d140304090c0834050c010908190801060906140d021803011a030a022407061401050409030509 67
    0x40d101810340c001e50310a24007030000380404800260006414016000c0c0e1040c2017425104240743c1d0b0103503542c03100000a080ca48020f407550307152400c4009001c0c0a100204404e1900144818160300203411401200c08a000700004005071050f03504103085445998499001480a207e8034a428040750354201c3c001c028104000c22507110090941c0c0c06500035010ba1350303a403500d00d1b011562111400303038400d91500c1c01c0a005590701d80e000c0b24403119458800914484003014941d918494030a6601010401c802403207000d11900d01400b1540118250192318054000c1c1c13044054481e010080c100c510545480d40e9460400d01c04407008a525440f8184d04007040203040e4801a10b0310007840340c003001a04500014848400301825101c80080b030f40810142e100d60707190b071660042070f03c48040b641201c3d1015500a4460800e114008040f4080d80c195000300b681c900340700d001c2e001640d08070030071440700c009070782c03141c04200c102c48100318050b00046080c418100182400800c2c1c2c41c05411490920 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 850864424 1250 850863174 850863191
    0x18040b041b0503041b230316060c0b0c03010b0313020a030c060c050d0306081b0a0e040b16050a0507060e120406230c0c0105030c040305010c051c0c09140301 69
    0x5211188500e1107900010b18008104010701c00e942d089000300241102c8040070343c41c9400d030200d08504417454100940420200b8072100c43e03804100505098141c0240020401c2e42d62101402d01d0078810010386070001440300103400c910307501c01105d040c0c401c80391102d400c1d619007140c0b1f4000c900511000b00c1c1c225000705400302c04520300e042d4113130091107140d86807400c0e140d03a031800906005110b1050700c20306003080400d02482d4030220360154028031000070011f1851351407000400700e60496000c01c01214003001400700b8804099400e5110f5000c09903003d00407403103008200c50600c2581303108800241d06003c15030009031103030024440755002c103040300d01605504040442550065001d2030219151000d072946042004000640f02441d07051414140320613102c05a442b0703a40d800d0b145042180000000c1c0d0f018000c00107680180da0004002c010528400c42c0c0a8000d83c00100101400115070800b804501e00b0341c000c01c0c00c202e0580d0b5412000c9842d0580c0a1304040c80048400d0b410b540300c0703806 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 850865674 1250 850864424 850864451
    0xf0c040f0e15040b03030d020703021507050a020f030301030b0a0504050109050d0809150108070611032502040b0f100e030a021201060611060408161a0406090303050a0218040b04 78
    0x190405403480034050681c03400c051401001c48191030300820300550030305075002195039011090b07502e14030100c81d01695504541c94224204640000c018105400140078000c49652000141111400c281c0031992441c0001030f140c4d9030390000b44402082202c0310f400081da1b00001e504142e0704a0b1003500003140c00c10b110307910641006080c04208000502070303010014681401c010703035892012034101556840d414450300d280c070380c3c1c0140a07041c207004c1e141044642c1c01c8002c008075880d140e00240c20030400c004455040d0140041184181e00c92410a4561005841c0000d5604441d0200425120303030b203e400201525600011801507505009540342e17100543ca5803248034003010510000010f2680c10702c80007501c0902901101000c4ea40300380304000020314000304440c0000340c00c0200140703218540c907040024a444071403100b00c1c9072100040c8010000740d0342140e4072407071194406100590320212004c0490240d0090352070411907844e03920090781096480420101c0e40500003180d01e0160750710 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 850866924 1250 850865674 850865699
    0xa0213030503070b10090908030c1b0a031106150d020103050703020436050702070e13210e03010c120f020904110a02011407080c03070306090c051e030f0f0c04 70
    0x140d0f01090344d1000c201070240040e6150001e4000346034208800200da0319244428000100002c00842c400508181000b0005007038548084192080b50040a078520b002080c600800070701c40c0c41445868041915100710540c8110250806041803103042c0c0150011405400701502c24001c0c0340c1c0c2004082004000c01c003011030810700045401c0c1154a4502c4d0f140481c0000400442c3c500b440e080c00e02241560200700e080c101d0b00700070101c1043d42c0ba491080405040b40300d800800005030462174000860011014820401c05078a591022140701002d00d400ea41c0805e40000024420407507031080b8000c02c2d404024140340c0c80038014102010070010600701d400006602d0358801c00881d84201090b42405081c8110840c0300d01c26100b402c08010250400d880602140d1000c4000300000e4203030340c0b0982c001e20003072041c44014494240d84120152080e07205141c0209100c856141e00408600b907001280e00405040d4900c09083e91055a9540c41000c06041c0d0301c4940d0040000148444c03d801 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 850868174 1250 850866924 850866937
    0x150607030518150403050609061005150408010903262a0c100e100b1003090206070203072603040e01090905030c06010f0630050901200a0206011a030a0213030503 71
    0x207003c207540350700b541800b0f45000c00c0240b01381500d074003980400c403811107a0a0400c04441007a100086078044000b4881c1070790041e0f070040c00b5035610700311241d8103155110107001500100426101e08804504446111038402203e8071036040710f203145800801808440600100c801d00d4064609050500045a003008101c03130030900c03030b01d07140e180340104000c0900180003003510f82c4004220750000321010520403128009082c05140d902d00c0311406540702c140c00c440e04141d0040070755100d65210103800074012207c05008030703c140e4100e4945410400081124143c40d21020110702c0c5a181c081b0640140c40600412590360105200300c1c3d02e8600e04018140c0a4041c503024002c03040e00f0640300401c0e0140301140c0401303502e0b1903501d403158080b00454111624642e520041034565810b140380740501040b0011401c84a5161088446003502c2009011446400d50989030144da95103d00f41103070440c074503242c0284c50100b001c200a48000da00405010040461184825903a13440300fa06680122 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 850869424 1250 850868174 850868209
    0x121b0613030207050307061e05090904060603030809030a20030c030a020706030506010e0907030f0b030a11130207020a120501090803070309030f02062a040f1805150607030518 77
    0x2030441003010b40502c0b0150142205030003d003c80340c41c1c40401401110108407508410b200340100c0e10004d44070b64212500048040c0c401030907401c00d45800d00040240348401d6000400f010041480c000c00441200c1000304c0d9595420440302c902c2d40303201501c2e030744c10740100c100e0b1108000c0040e815a050025116001da1900940a2546131131806002e45030014426410424103895100369036130b8007480c00e50032075010310b0001490b030403a0840344014803019074015498458001444100030b1810343d0410405002d5070080c02d680c03400d1020340242e010b0359034001d610120f03855003404032240004010100d140680c00201c0c01202540741c90700564001c0d1810000a03844e0405d03017080c1608000c28103002c84440c4000c007078a19182d42000454905082c0007075841c08000b060090700d074420700c00c0d24064002819208042556040503566811880d02c81c0c0d106142050002070304801100c0741c11140c030714040c01e050b02e003600c10b03601117489034001e4850001a01d900340881c5000d8070f40c00b51410411104 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 850870674 1250 850869424 850869451
    0x160302030409060807030c031e152906030c0304030203090402040f050910210305190e18070c0b0a150b1b07080307080a050f070606090b03010c02121b06 67
    0x501d0400b5096034019000100c45500030201040011545108001120b801890350481c14520302c4980e1102e111a40000d02450000c2400342d22180c01d03a400440d40340c00c45450780b4102002c111281411140c14000b02d80d1001051002584180d0500700844d441842031041d24071b000315003c0080c080380c00940050b004c40c1d44002040c030003410582d0016410a001c1c45c0d400c10308501c1c29401058807103155003418503c89544d4542420140200e00341c461105031003d5a00d5136416507d001800071a050b18468400d640c06003403810180102d02c0500c1c0601802da54407004000c2c1030711210700c01803014105040c1280e54140c52552b095103a00030a002d4110440e04640e5154548030516045956040202a540098104110600001044410b020390116016031105000c0302e0564203402041c074258100c05000541c0d034100861980b080080d210368480400480791000145405c071000c542c403200151f84000c0b28a0304000c040400703070040610000400d82c000912907903190070700b1000d039140c0382800340 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 850871924 1250 850870674 850870679
    0x1b1413080c0406210314070f0605070305060a0f0e0c0c03070b01091a01020c0d020d1505310209190f0e100509030406050c2a0102010f020414151603020304 68
    0x300b50050034000c0540519801650018035a008141c0b020500c004007840764407001d100c10039401c54151600d003a0064610403514009083c5103000c2c03c0b085840c00700080c40c240000e051403500203580c1701a102c0d808500c2205900788005030060100103000e100003030398140400070302d02208000409609200d42d445a0b115490070407104241c4010b106085408001a030403951580d83c00030340030b00c0c031101c222000d1001c80b000d07002062101e94400c00c05049110b4440400c241d000c11a048a8001c6d148000744261001d10a8101c4800c211480803002c4001c075a00d001402610700319440d1071700145c0102014a115015441c8602196a02c08648030303caa210801004515014450501150310f0480103114614000c030b403c03612403103903004084c2440400300300340c1c8215408010440d40f4075400007078040d127580d2251986608407840008035005600740040d400c1c0040407402a64202c400640c51020101114020070602064031600c2049141c41800480030407241c41c10085100c1d8040e4025598650 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 850873174 1250 850871924 850871929
    0x1809020a0b0405102f0a03020d020601230310020d0f060b0a23070215193209031002121005090c0a1b03050406121b1413080c 55
    0xc1160340100c4110030140000c010603107901c81881d82c190b00600c0c2104411030050400103c0c5910f581140440300300c0304030751414180300020044074480c001c0d000c851120b181544102d9540100f4007510102102907004503201000c0700c034008a0007a402000d030341281480c000301c08200e03040704004000c095246c20012289107003511444002c1d200a8a0f62850808803000103080c120031914030b81191140216001a018003101c1901c6c801070b80107081e51560880080003a009ea04110140d40ca101c1c6548030b50a0b0b414042c95006225801000c100c100d0f00440300300c100f5000c5000ca15139011791108110140d042c1d0f40034416201d83d5415202c0050f20b404200b01c9c40803688100424189601c200540203101030383d619402c0c980e0091000c1c1440c0c1d0341c0c6500c407404a40d0340e01c800c0c0300310320b6150f45041143c041681240141041d1501035680e14100e081a001d42400d45d00b2074212900604d80c43d641a40805101d61220703c4800c50310040c0da0300e88440500820003003ca50b07070002d1010b0f000100c0000307551 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 850874424 1250 850873174 850873189
    0x80c07051f0b06090907051c02210a0b0a142407030e01020d020c0904080903010c08090d1b06090614151f05090d02010e030a0f0b0702060f041506180902 67
    0x2404191a00fa040610703038008107410b1070010b03104505112011030003240010002102818058903c9015034441c55410b000341c2e140c3c4000021800507601d481d0014003503071614800c031400010001c000641140c90304041041640010340c50541151140d0b54904e0304503035405110a085440100440d40d030031049c140140440c1d14480d4883c1150440718140011560000e02c00000303c000300d40828554440f0318001940c0d118001c00147c055003020301c1408496008620740d44900c2191041c4ca00d0751207001400c803202d101e0b0120840101042c0c00142d400310b01c6560013031450f54421807001500701100501070040110494050300e0404d6203442c0e00e006803c101c440940c0d603d45085400404822a2402070043c0c02040e540501480c603041d0301400b5a0301c0f42c0c269040200000c0e054681c140c00700c2c18407412090341e441c01581c1a1014001048c8071501c0040c0701c0f0303c903215507441860756482e00c2d81e07010a1100d04404400c40b458a0340000709405103541036010307002d0b40d00c0c400022034052034412301121 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 850875674 1250 850874424 850874441
    0x181f09051302030106050406052101060f030e0c010f080603070509010e01030c0603050106091e05040507050d061d060d03020f0d080f06041505040c090909050606030f1c080c07051f 79
    0x10780c01800100507198001d010303102a03032541d003092a03e07070b5103270580080c0710a04000e80c0d440480c000c000001e00c00da004103c0c03003111106680c0a101d4105800c200c250341d44010742c4074500080c001c3c81c242c90164801c0500a40100c80207084e0381c00c950f55400000e100704800c2c1c012445079415000100200100c20812000800a40c28140a030398500b0384054580309040c8a10314105100794101011002544011005058004c004000c41d05106000500c145c12a0628400c514078000003c81d40951000c560314851455982030140d039503c900c18072940703103400b440c1102584510061414449800c3c0b10114221070180d5520b0000c1c0342507450100007079001f402980c0940e10340242c0c0c9201c214090042000e4940c11780340030891a40d01c500880d2a039449a12441c41249001921000c00802041d4540251812811540300c82d440031341c4551505a111031032030100d100081040c4e80a4023911078994000b200c10000c03818803901391225410506c07101030482258a03980c981d00d00d40740f02841070003031 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 850876924 1250 850875674 850875709
    0xc06090c0311090a050603060112060f1103160e0f0607050a0c060f0f210e12040b07020a150e0f0d1e060e0d4404050c15181f0905 57
    0x17044c00c0c660702007600d4000600404040c01b5000322100c1c1401a15003180301c030564502801c12500c90b0006640600e0f8005540c0e103a45140240014446c81d481540301d00e08403003000b401264004210005c10003079030302c549000c4800b07000369146030000c5010461918010440d5444182140742d01460040c1281082d0300040f00340065060040c2d8242c6514082c036803102600f08001030b40041998000d81b819118070244c1460881c0040d022801c030719104040c10189101341e900360110f989540320f500009038103980543c0003500003800b140c214582045180290100a802c01109490380e07140e0519032808003180d0901c031040c00301403604010651060010f03400c20600a00280c1012010041400b059880041c680b0108a190380c07407200c104091f01d40100589640d28481104000480c01204000f00c809071054090054030303404505002c00da201d50710031000804ea18054206864515401c0b1340c940d01c079003000c25041102c800784241d00c6000c0b0304000c0c607142c0500d0286040704210710503025203070740322 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 850878174 1250 850876924 850876931
    0x9020408061303020c030a03051e161707060207060504140715032c060114030a11100903140307050c060a0c2a060e011e050a0c06090c0311090a 63
    0x142003004200c1d190025400e4540c82000c02650504a05d0701d00540151980f6009605000c400c15802000030f01c43d0302c11010303491031501c81448400000d4010320f8640303030802c040b1150b00b8000642040c2c0c4081c40f0800e182c851400c2464544441e000c980203004102c1b1040e82d1641440305200601620002450a100c024009107080204800c070080e02e110f01e503801d051311002644045085102d008040c1407114810f511a5484040c4844d80d484082c82543d00c508100e170808003640c01e0120340c0c01021600700090800fa4048241403003a414034044000d001c01c00243c03008800208d440c00c0b140c065050300c0004684801c0581071175800c2c020100c1c9100e00c5440100a6100074035044501c080c074403904181284a00c0056146046440308010030303110152103141c1000c0b0f01c1c00d800c1301d0044c9944400382e0714100141e050909c20701c26210101c1b12080410020300188140c10701c10240c12070094860700011401484c550b803100c0c20103501d60070455034000b0f500c00b4090107040089010740d00030300715070060 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 850879424 1250 850878174 850878179
    0x507020115180209040e06070c1b0806040803090c1306060210140a0b0111010c12051f150e0406080105330402031e0a09050c24030403021f060906090204 67
    0x121490b48441d070241460700411441559030780c90f40408003c14a083c01c1c1c1d025442c00080042220701c28003000c8920700b4901c4030003200110a4501c0340c0554900c90020700e01c6480b180c0751400550401080050280310b0b40c6031440454541d0740e04000100580c43c40030441c1c5091100203818610307910904010545803066101045c20031358007081d00305200507400510041d81500480e8641040340085030150308000c9203036480782d400381c102030524500181c100243c0c2c40da40031444802c0817400e2811460400841c05005480c1140114488400142800c2c4651400f040125003601c9495214405a95542c0c0410881500c00b2100c0a2482e4039045034050410808544102c0035401c001c0b014003c550100016040c404818410031885400440c0185d00b07182174143c2c0c07030261144400460f5580070792280c240e284e0501c005210181954001c411040091050b080740ba540c10040041d4114818111041c0510b880c0d03108142e204841c0d1100441d9050403c2741030ba06484ca0f039800b03043c0151040004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 850880674 1250 850879424 850879439
    0x9090c030f072109240c090302190509010314070501090e16110f0616030903021c170c03060f120c0114070c0803030f07050412020120030d090528030c0312050a0507020115 75
    0x7d400903250304881002002d004032a5038000582c2036080140c010302d0120002c42401810329004000e40c10000c1194000ca07207030b4004403107c40c0c1c148201d1b1048100e5201084038000009403414500b5114980301c03828042c0380144c0b92800c060503051102c01d4100800b48100242100600c00d400d050360b082c140200740c81580d00954030001680e0101900c485035074079030483e510401d0080c03100743e8081240786850800c089081d41c05d0b40b044c0c07401441100c20780e0350300304a07060451074402c1ca02503442c0505029a6400c3c01510306140380140391808010420801e80018015018840589880d07030045881786401b01c00e903070134844041c0107407003407000600c0300300000e03003400202c1d540c5103a0a10309822030179000015500d2849843c61070400900000c580b510440c0d086a0001071f100703000d28219210f0060103010500b06030444520910b4406480590401007406160304681051080c603140340300040410b8002c080760b07070070b94043c50391a07103c1d018030112581c240548002e1f4040c442c1118000361910700d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 850881924 1250 850880674 850880687
    0x606010c03080a0e1b040c0309030504270f0204170c061c02130608151c0204110706020403031d310b0901090209090c030f072109240c 59
    0x401001c00000030b0014001c50071a400c44500078500000701e031a5851307000b41010002a1815003140154607140720344040501ca03019441440f50151110b80c5814103260ba07004540d00d000c0f410070b510010312440c0108482080c440c81e5031550200074010f840b6402e0007852044818040123460325035004189401d441e694001c116145c403201000b010714035282501c0b42c030002c0c0c001d1101c1200341401110001421503003061216101d034a6800d48603042140c3c1d1010040703e440d5041201216100c011030403c014106944200030070354156400f542000350960b2107100380c0c0c1c0103800c1100010b0010466203107a07507855501405610301102c0e80d40045001d858210b420305242404049000c070050901d2110945c036034003220740d00001900c0356907150384036002c01000c1d51290520500400c242d9000403505a2110207032405510010380020140d2110b04084030120071441840c0c001045425041910140700e20035015039520503800e80503605121324003108010000c1c0d030205580b50410144440c015804071 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 850883174 1250 850881924 850881947
    0x1818090d0203270a05090403030903090504230a060e1602060a0b09040f02010923030607020c01021002180a03120305060f03070e180618010e030403020d080702150f09030f060601 78
    0x1143d40f41888480001c1e040055540f2a9810080e0081440103040c0e15800c84800103029444002c000303941c0b03d003407000700c03441548031143c05605542240d0392135504819a6801c0405030782c011403200c1e1a10301003a01302e1801c0d45c5120542030820310058045406001d81c55001202813810089407a101001c60844000104000c245580e40c41c2c8650440e030040b03c52402800405066400034011a4181c911420000300528824420140001c62481c400654104c1600043c2d02600c01461007500305c1020b900050768070b4506804a2503940c0440c0c0350803248200a600901301154524400e001c041c045030800740030310740214404041c2d440b0b2500c0014808044032401c2c00014920b541e054800d03440900ba40310f042d407680c0561014450595070004009030b610701a94001c01c501041540584e0303480c400d078030009400c51a1400e0070008110032101400071140050582040111042032883d800d03488502000b8515130b02040550350341c102007000450200c05000106507030709100d0000380c04440c0d0300 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 850884424 1250 850883174 850883227
    0x282114040b0a091203020405120a03142508070b1e1b090306040c170a1a09030d0516030b0307030506060609030a050109051c0503100303051818090d0203 67
    0x70100310b00145550002007240c0e04603007804a807807010000103000c0d600500c03c46101e07031184660301c402490086101402c0c190700d512401c0034001815140003164201c511406c0401880303011591601c04190301c3c50b01094454420710780c0e21001da140200200c0800b40500c0b518000103110302000800384628240c0049400b10b0651314803901071240d490900c9103082d00d9825010340000d020420240b03002c02000d40b202c1d4050002e00500b2113001d0b0790380703148114015001d100c03030030361904103214031455079070b044008035044c0e0f40750100451160081e54030546815400310154001c1080c0940e0610a4845018046003d03041c0281782d41c881a5807040090940c03481060f00194510483c0e404000202c442c50b1720100a01c81320080382810383d191152186582c2a14038480c4d4440b80052003441144e00c18082c4a1541441c3d90841c4c5086800e60084600100c102c41e072a0080b02c03640c0e595441d2a510310b4410000d81c1c603a49004805c1608110100e07103514295803040c07007003401815044404410380b2181c0c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 850885674 1250 850884424 850884443
    0x2030a140c010b150405091609140f040c02062a04141f030605180f190f0e0109110609030303070e03120315090912040501030228211404 60
    0x8020300c16005100f50300025511041e1182c0001403000f10b0300c040d2044a8048494941940d1017603e6241400313440b070794910024034031203018001204100c5100320042c8028103585008045500860121915490804090b078840d1342005400e1090640160840c030044080071307541c00441c42039103054000d038020003d4002d84104800309075283d0450200ba820030907110004064000700025008080c94003815000b20800d98941c2039450000d2041401a102800401000d94506400c406a1020710b0250603095032642c034400300c1c0001c81c1c003c04e040d0325014400040c070b04500d454400500300c0b100c20307400c0c0100d0703041c1700c220072543e0084243c0754810f8032400c12405010383c1c240004d040c842e1040c00809403000c080248400c40c043c08901c59036904090702c920301f0546444041031f0351195000452801c03650308010501455110380c02800c0c0d0306007941d00e401920a24180b0707044140201d81302070000584d000c1014404a64078440f0050840b0080c9010411481c20390700c2c0400c072800007400900358004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 850886924 1250 850885674 850885687
    0x304061e0227130234030801270b030c030d090518101205010b0409061d0105091e0f0613031e0c0609150c051b24071b03020a0c0602030a14 61
    0x754004050070040b100410f004017112900c1c0c002888860b145040d800034106d10000f15480008410907503200100c0c1c0144805007003441d503c0e2000c2c100b010701158050086000000a43c2c400700824031820006440c2e004400d406c0c2400d000002000300c0e0700b13000c0440c3c0e4205201d1041c10321202d20081d503585400014082d02d0790b01301680942003004c422a0018a4850725206011a5074015000441c0d000103808034804003861041c01d82d40706607040710143d0081d1035041a145003401c50000303402c80c0441681c80114020b26044d09017001211004a0750520340710300c1042541c45000d01e07064003500c2512022413462400000d1900038000300081c120b035a55403102e0203000c842d00c503200044040142c01c0c0550b1070001002441138002c60400c204d0006044401c2d1114000071400d00d0102180062030380e520340100e003138900728100203841001880f1904442c05076012580000040c1c240c081e4008014045452502000c0f02070698000021034005200c44c201941d0b00001e040c0b58642c480d9510390f141c49 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 850888174 1250 850886924 850886947
    0x106021b2103070c0305010501090507050a090b1c0204141011070303050d1b030c20031c0908031f0e071205100b04080f160e0c0304061e02271302 64
    0x4543d0714007074100030500b10000100041500103d041e50002c0c01c0902c2140c0b5800f805071028003580d000000442c828000900989060300003400c8800301f80c00142500e05101a1510200ea11a82109071460400c4139a000107045c03002030b8043d101034030b00e0029090000c40c01859201c00345400000d04011000800308503000c0940c0040b00c0d00311000e0b840b40800307041c1807005002804040003903c089070410302021045100400c05460984100b00914a04508091340d04c143e2244458100310380345e40c5201ca84c01103075501e03025510401c10360700513182915010941b41c1a407860f59100781c111034614802c00079840d07845614008030303800c100d070041040d8981c0c2901805e80c001980026400396804030700040c800f0000140d07070103403404007400d4440003200900d82c8a8801305c24090344140003032000105400c00c10000040d6807060081c00c00040070707100c205054071880c0c4c6e40b60381e01d882240c020480c10142240c5103003408d60298100260580c180030700011910039415019a843c4a980c00f107900d44090 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 850889424 1250 850888174 850888177
    0x60d020c030913050f010b041a07080d020c07030b01050901030c0501050d0b03010c050a0908190215130b2a12070f08030a02040f0602010e15131a0106021b2103 70
    0x100042454031010908801e640c000c15084480c40728420b03045d0700009510300980c040b03405a41030100c06035200010743e0401c442a40c005a804c8407440e10410400c003058440c0d2001d0500847c040001e03001162442c10100038a605c180c2015110b0f48800d4010400030752040b5070031040301c05c2030a1030344e02d4800e00e03007184d03000308400c9440c1e64040d401c2070703c0d11214680c0b00004000906450311041100c0b07403202442c41d5075014028050a01c00e841d41c4080000d46400480c04503003031240881c1c1d43ca8566480700c00220103a20707901a00040601107510301c000058001030768442448c007281460260902e094007540d80d040030080da40298800a03e6509102e0102221903603250031543c45666424409291002980541b086038146280705c0c5000c0b82ca1031040c000c4100ea12a040001c00d007070300205060001d0210090425013050708010790140012f460300f20142d80080164400c0b90700d96143c404041d0400c4a0114820003211549100e144039036128401542001181103124481024040700b5900e10b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 850890674 1250 850889424 850889437
    0x2030f19260106030e03030f041e1e140102030601090303081e04050a0302010e1222050d050c043213020603040623131101090b0f0405100509060d020c03 67
    0xa031600c030080007a807992260103412586295410486140c0441000d9224001a145104184615400300300814038500c2c0850000006000a4480c1d40c2c50342e40301c02d00111400400440d020380202c0c010140110340c08845519248000203602d140b91103c0000c00d80311440c00000e042c0328001020604500800c8050515501001140c001c14205801c220b80c0c3c80350701c928110015800e10301d400c000440c010480349100031a9054407414514a01402660b05080d2600c1d0301003000c2007903000466a0301c1d601850407050003200a0400d08140c282403000b607500e42c450080c0c4201469002c1c1c4040102d0301d41e111540a507000d441c01079078581e03101a00c441615500b010790f0150000c824801800096440a54170031541040d941c0045200e5032100560b03001120340303003403800c41410a40c01269000784001c0c501c001c14542100080d8075090244e02c181c11100e48d42030780c82170228042c4040d04060003e4a44400a4101141403042082c001100e0340305180326009400d4000c10002582d42003041910324 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 850891924 1250 850890674 850890707
    0x1d070207090903050301030212070f0603020c030d18020414070507060e030408031b0f060f0f0612031c1524031119031d0d111212010e010602030f19 65
    0x14800b25428010265042800705910481505070307401c800d48130003e2a030048400010140c17208600e007a0050b0029013000480480307e0204010560744d0310081e100d5806040400d0001ca0070000f014014001200c07101000b06100001c1c0000703100b14070ba00041a40d1149901890204d0503e0250220904500469100c01c0a510001c181544401d600f0b1803140c002e0b40c000c0b400c442e20b114402e02020754a46007070b15082265010080405c0300e00d04000c80b419030110025040041d0455404804c40ca541d01c400b14001c188800e0032481c4107824860b00130021600e02d04180803c00038282410070001100c980f03040d40c400d0080c94246440f181c042d401c030b01a64a4004c4074145c072592401041242c1123504014100080d01d0000030750005c207000700c1440414100280104500c40d50007a00751010501602c0c002014492403424140401c0d14000500001c108040c6144041d458916181d4008a068101000759001400340c0c0002a02040a44101c0c3d4080310102500701c1c4851000e4a500318006102070 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 850893174 1250 850891924 850891931
    0xd140a1101020406030605130203040c060c050c09010603020c0106080604020f09040312020414010314070e0405090a0f080c010e07120809120d03140604060b121b030106020706020c01091d07020709 86
    0x113403080d0545c0c448000c407030054400800203100101c44200324481110001c11050020100f404680e100d46082c8005501c600122540190000000703503030b440090b80003400280c0c000074240b410380000c0c0030b081c0041040100418040c10700780c0c00154441c104000d00350141586000180a01d48986803510f0307079413003100b0115039a0351100d9688007000c64425101d03011900301515840310b10741d1949410b10640c0e490340c405184036801d4040001410f000343c207901007403103080f200002040e008000d20200920800b6081d99510300e000c210f60a4603800c2c0c1e400c4006800c601400c2000c4064407960300f0085511003c0c980e920308812000801c4030500c0c803c2c080c807a124050900c01c140e42c00d64000740c0c41009100d040802507841c001000142c0d0b5540c01841e140c110b0901c6941c03518103403403444030f03080b42c6100011240340c00c0e80113007801c5c81d410907404280140d001c0102000295014000f03030000010070b180406919082038014401120101103060400450300c00280b45035200380a094040d010300841030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 850894424 1250 850893174 850893179
    0xf0b0a20071d16050930030412110303040810090606180f1a0105040306054506060d030806121b19060207060c0c1d07110d140a11010204 60
    0xd02151003c48030900301d0704010724081d4149014034242c0d601e102e0020403000100205021066a04c0783c040140e4403240415014000e814106002038405031011400345907050b8858180548410031007107845c5d0003030b00200014001450041a441c40b002c0150101041d0781d01c161034035000408050b40142c42c03c0341d40795156548081d81360001e04d0441900380d0144030020076810401e040003580d0f1415070214004200420015403e90070081d4440f0f03161018000e00102c1d028140c54a00d0740101a9120112000b1901044005401c00f800740e0b0644c3e000410315860710b0780100b0269010410054140081c840c0019410381d03550741c4040c85e1100080a845111881c0110211001c0c0d14401e024883c12841c5285000d60500001d504101ea2a5500510600d481c0c05c8045e0b4501e030519100703682c654807410010448081340d05100c01d040038407a201040a03c0c0c100401000e010120542c442203800030035440341c13900c2d88003203128694103802c031211b44e45482e00c10f420781d120041c94051074140e50021600 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 850895674 1250 850894424 850894469
    0x30118080403031b081206040c030c020727020a091707060c0b0a0207060c0905100513090e120711041d060408030a140f06010207080d02060c030414160f0b0a2007 71
    0x51f002e600269420b100d1000c0443c400e80654004055050050344682000c0240144a4042030380040200046c030044e84109150038007668400c1e0706800200d0300b40a010422540d81d001d80360f00d80300500002e4403080781070890003003403c500aa805170080ea490000300c3c022081e280c0c11a4525540540100300000c2c01040141802c03290b8031a192080030600e84046001d40201c080381c0708a01c4010f0503808490800700c000005080442d241001403040b800d240300b0311204240102036480c0140c0d1034890203c540300801082c0c4001c80e8400058035a030805104d00c0d860002400340d00b103a440001540c03280c0e2040d038510003d0503803540f406d40c807501441c20b11144110103201d80d405400c0a90039220b21644505103d0b50701e0102c905600f00513481403001503000700c5000d010390741191141550304050460b44200398502840c03101a240c0b01c0c003407079500f0007526451440d410300410f804401181400c055840107400c0041e04c0302d103042c400c2758051011100d110140502c0016008006401e0316054480c1c18 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 850896924 1250 850895674 850895707
    0x8130806040f0c0518060d05250e070f0516082704060605072003030714060f011a0706091106040b0406030f051012050a0606060509030118080403031b08 67
    0x101074542074407590f00131030103080c40003040c002c050505105c002c680c2c0752082400001e00c051101503800b4003811111007030042c4010900400c14414440c0d440030355041c8000c500c3c414501400304c0050020301240701883d5604001600c05003c0071642c0c0c401e22016a09225080703200c0c00380341c03504000e440704043e62134860010207008603d0003518208049522050b0036251849083c00c0604860904100d0009910703000c03030001103604000d03050701d04101196032112040c0618401010300c5412600030804d40030741c0c02485134010094035000190181d2407000003030603032003121006444180c9a0558009112820600c1c01d40424017801d115640ca40e034010a0a482d0014022800005c1c20000301c04c1c000307101c90090b00d008104513508072150905d004c10b41121411100021103417800f0b031403168004140309104020040c41c1f00e0f2990355540c0245400c040c21213019429464140d480c0c00d80b4840814000025181600d9050420381180c0101c407100d4400031a400c18000e00c42d1000044c13411502c100241e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 850898174 1250 850896924 850896953
    0x60c0304091404020604170709020a1e0e0916091703030618090d030c17010806180106181e0e0c180412030209040b030f1e12070813080604 61
    0x5000300b0400e44041c40c14020040e0988001e5844403052009200701c0400e81c0d803100d6480b040b042103c410a81e60580603003030340c004491043c0400d506c0503031843d03021200f019070f0141010350b1800250130714940d00000c1c41c0c400c024259841d000000e2540340101d600421000f009030a140030394240301d0f030030315041d40d03502da00454503075015a201e244c030801c1d40700b2030402250042507190064074044a031210110010a00c0350240010401124030350440484031240c00ca000c1d05021700038144510700382440208100c032092310403010b40c1c58003c04110f40150200090040b210841000c00c2c881820924000d0641108a02c1a411451300110f101c10400000388500d180c001a00c00b04104000e1000c090796a10084a0240a41492610103580544294001e100440c03005000050302204400440e00c1c04940ba680e1524031340c40101c8905c110028440e107019001405030003031002051014813a40103000e0b0305802013106a021451444141c003040440c1d014041500c00c0724186c1c40d01c0d0520741b403504801d4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 850899280 1106 850898174 850898189
    0x60e0a030b18071a0414010908100b090a2f16030c050c0d050a0f020123030a24030305180d0812060301060608040f030e060c0304 57
    0x201045019102403108500c000c204410b00610b0320600d0303000300d0803510340e44241200902a0604450965801d50200303100c4da5104801600d010701c00b41c102044901822003004c4180010741c0c49401c0c600400c41c1e880d00107840702c1e0040c41c100c1d0044d1920b03c14101c001c0e04600400c3c10f030020845003100b02213400c103141050000d03002c030341c424015031f00f01d00080300090050140141000028800c200c200e400c0c99030900c0d1581c50076035800003000d00802c04c014941341c032000c2d6800391049000c80800708140c1741250340d4070303180c0c0c1880750300460741110f0301e40c030b42040c0510b40c0e82601201c3c00c201d040700a0007041c950454409031020b8001072411540104514000140c0d6280c01039031000d82c92180b041e141e00d07641c030b004410452940c000c10030383c0240c0c940300041004603840303038802e900150054009000d83c81c580c01e08490365031640c0200b640124000520020190002000f0300460b0001c = true := by decide +kernel

theorem cover : BRFrame.Cov 850719424 850899280 := by
  have h0 := BRFrame.cov_init 850719424
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850719424 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 850719424 ≤ n) (h2 : n < 850899280) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
