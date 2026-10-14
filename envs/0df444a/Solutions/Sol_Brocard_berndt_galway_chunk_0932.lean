-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0932
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:02:56.27934+00:00
-- url     : https://prove2.me/submissions/bb63c530-3dd7-4439-81fc-a3e6cb48a688

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 167446043 ≤ n < 167625899 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 167447293 1250 167446043 167446063
    0x110304031a1015030902060d1508071e0b0a020f01020301030f120203070203150a0e060f040c060206100b030411040e0d120b010203030f06061b0c010305010506070f170903070602 78
    0xa4010075558409902a060030580504040c94041c3e05090408a01075044160b0040c8005d20080c1020580704190f0200c42185804081e00082c20301c2c10007580b50705000010140050741000c448420014640c448c8115051090700c01d0010005015a980740c401d102c1d104840c0300002c002d40d0340e965281041e400c2139aa080c1c0581e41e55002c021000c2009000008640800340d0290180c4094210440840c401a0300280210324079030321080191040c40c800c0c00002e100d9200140d2083c0d040c2864184803200280d40c1e003140c0250b503c1075007403021100d0264079403003c542c042c003a0181d40707580fa4a002000d44503501e0b11160410308141d07078100c41c042d020540c442c0b4601140d90f000f0b21038160480003816955628030807405a001040815241d03001d10003442d605c918060042c0d890140e03815203940302d840b02001c008550360000b4410500c07a6a060151a00410341140c0b21030914080703031901b0807840a00c103801000d81880f5151044244007a00c161071360341c1c0700142039600b52a0746290194603100200c4e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 167448543 1250 167447293 167447333
    0x200a020f01050301060f21060306021206090103020634140c06180625080408010c08063304080d02190b0f1306021912090b0604020a11030403 62
    0x303050250355102e48103580c101c543c0c03903454400341e03881805e003600c030fa0800b20b0400b200d0485440740b1000e04403d5004d504005c51140c0030050b5030310322014003010f0f541400740c81c01c0d21071074040c2d00400241ea03582e0252560340907290280080a103201d11760880c0c840000810100c0c21405010000501890300768003411952408191b400c1018140304006d600c2c42410305c0c0900354103d0300c00d409120b0401c1c4002c5e200b4144030903000c030710b401d290350003003864070100d100e044594410001c1c0c14000d11303800f80240c448108807814070540d2420854000380d0510005440d040710300303c001e030b0740d200c0424540101580d1011074915890f544c5487c1c81407291200f00e91500d03180944150a0340c0720076002c81684030039400781c105152185030380364090701103400c00000d0002d00d5040b03202d0130480c020401e18401010341c80c01c42c568501144c4e01c03116014085e100d402540d1482c841c0b4110000340884c070407044442c1e0111041f64010303650b0070390960039580c040c184860070707910b40b0021801008110000000c02c3e2545401 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 167449793 1250 167448543 167448559
    0xf170d02031e04030c0f0e15100309060b040203010e0117070b07061a090a1a01080103050706080402030a060f060302011d03100b010918060602010e0d0504030f020d0506040b0402040b01030b0307031101200a02 91
    0x60303001c2341603500c01000d40181c09110210545132103548a81000b610034000030841a103110009400d0343c0086e004104090a50f20041141c40c03046451150b030241c060300501030851800b003110380c040c01180303000b1f0312440d03c801004410340750f08017445070402d000804051503401e00c1c0e400d100040480803d540c800140a450000b00c41d8001d45103c0c2c126076019001781825414441e0807643c009000e00100d805204c0c5550280008000c2d00513400340d80380440c000aa81855400018141119008485000d44038004020310300e490200f0340181040720300e40c0114134910300b0001200c2e104078036407000e1400480c1084000c0c0720001900f10310115819a4000c0c860701040c03075101ca03200c0c10003078281c502041d0200002c00001d0488006401e0740c41c0014100c0410302e1141d15513500305801100d040ba0b422010030200021450f0900c00d910a00b18207280821000f1040004603903900400c1c0400ba004100340c0c005c201090380310300d034641841d54901405419092800080f251307070384a8248120322403c0a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 167451043 1250 167449793 167449801
    0x5072d0b0f09070f03060c0203041701020909060d030e090408090301090312060f050108160c060e06040213021c020906070606121e03050d0c090f0f170d02031e04030c0f0e 75
    0x4005190f00607610b082d06460702e405c1c99981d03244010314042a04c20700b507000a001c00a03844502070304c21070305040b200001581c0c41c00143d0800c4041c140007000c03030380f140e010406810082544480a844a88029910307000a81c88504104465001e000d295070360660a21424508250703100c400d201c0400a06201071044945480815802e10901d0080320f0000d00321070000760300b140e800701c1c1c1004111950300340f4051903c4c59440d40d10580c0d5459941402c01c2d408402400110306003d003a0210401e43c0060860410030b01c030184142ca09080b07081c5004503074002c64052502c1d91010200c54000e80d1241040141650354101e00b95a010500790540310054114507100403922102140da2083ea07145d40d56920f8400f010749d08100034140900d100c01001103c7c4804148550b99400010280c960a0b682ca203010385406540808039207111550407054110003200003401d40c00009454901810074280d801a81e103030007500d11a0b00132648003030700010a4035000039628044140705400c0da410390954048a5503 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 167452293 1250 167451043 167451061
    0x50a110d11061005030a0210090e04030c03021501060e060a0311210a050f040b041e080405040b0301150306181502030117010b150c0a1a180d05072d0b0f 67
    0xf194850700340c1580040510704014075080d40c08140084c071a003410201191aa110510380d102d04840c201c0208180d03010f40e0061540400c00c5201090301e0501030003c41d8189040240041c5000e44d06074050003011a24bc4031141c002d8101030010382040c900030751200340b00f51050340b0050340000b00614800c1403602040c00442d0b6801014824200d05481d0304040e140c546e43d000c4041c1d401070043e03580203544000c1c403c08102c8103510f481d101c1e00480c0400c0e151410442000115259619072500c240e14200300550404400300c0990200e03508820006680600d0307101c18440303080407400c0184404480b00700001040c256502031030503609605034504401002c0c200d910700b02c0c0c0e01d88403482e13030040d52a040701c00c0c1850f040d00140780c5a080001922030003a03099071a031894400040030750010007044d004200c0000300d086c1000e685001e5000003070025801c01500a803480c4039101c0c014240340002480400340c41d4100310340200742000c03640c7c4403299079003d062070500143c058401c030118110440104460403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 167453543 1250 167452293 167452321
    0x703180f1a040b06061803150a0b030a0f060c02010207120518010c0807020d050c0612040209060303030424020702060d0906050115050d1a030f0d02010c03050c040303050a110d1106 79
    0x395108240300f403940c40d09020814140c002c1840945d03800006200d02005481c14030070109050f032019501d02c0d01c2e0070900014002c0d1040e9070b44240c020762014504001040080d02d000101d40c0d0421400181c000010b081280a4440e070f88001e80781840140700b484245034080000c0c003a9005001c4449042c0001c0401100c185000210181c454071050100d10003520300102100c4230705114004039140540e02601044568000c044001070104503001000254140801540d074009000c42c065440c600d4207540d4020b83c6000814580b90321451012086000f039502e50407149810f400921160725141e03020340c0e0101414001d44c0440f40c040c113000c00002c0505490300711550300b0700d1940f02c0c242001070000312040140f1000388210044e07851001c0c600b04544044c84080c859411000203407242255407180603013560032540d0241c08040c9400108224460294203031000c1da94149442d550710b220004085130000c00c6007982106500034918192180c5401190400c400040032080d03a10030b07070321142204000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 167454793 1250 167453543 167453551
    0x5090319030209041d1f090b07231b011a01050406050d020714060915040f0b06032a0a060306080c150c01090503071505041a0703180f1a 60
    0x404000c900940600e4000e40181c20202030140c00010002103c50041c1c4d2190441020f60030309801c024540d00c044190f409503496841d0010303c2c188800310301a5900340300c0341c10091460003040422060b4513004120035041300310340040c0b081c0c06c03a120141c10074032a100d05440446402207610300130301c1e4461010380e0200c103030112005841c0c907400c00e49000c2c82507405602031404441c4495003005841c2c0002c8a501018900929220041c21340e443c00c0f0340440d280c0f0300d817a00340d0220598540e00300000983c10242a41a44d6813104030101c20f0744800000c07a180c208510302c5101c0751a002106032030000c20f407200d54400c540703040303a0b046500c85c0c2e0f441c01a411100180110382090300b020b024849181019800543e072640c4010000345480c00d5400c0003400c480e50002c00716aa500700080301d4040c0001c00c2c80c0b40803440078102082102d0704043c0c0d2418903000700c00c0104403449028400140c007440c040d9010003a400400041d00f00c5c00501d900d880b040101c1c202d0012203124600c00c81c17800e49a50400a80d5102e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 167456043 1250 167454793 167454817
    0x1b05090702070314070911030a110f070303020d180f020306010519050405091614090c0918090705030d17010801111b101a030105150d0213060f06080901050903 70
    0x2c820300755210130744882d101c51101145881180c8000030407461902c21844c00d0292403041c19140e01309a50644142c40006203000f1490b03c0510402020314000d104840700103601d4240180d0301c0c0c0940c10306ca00603110105001000c11343e0303070240c081030102507042e02c07491510890644e20640c5c1c07503000b0001d180c1390301002c0c001d203000c02040c01e10803410aa03101076000b2502904461210f200c0806c0284516919002500f00c0310101021070084e06144210941003810741121504042c0c40350003045070387d9040c2c00b110701c1d03120300b49021410010051107820007505c0c029003958a60304590002404140030038900042107040c520001440d07007810b109042441c0c00a00c5003c3c903024003001c843c440c070082c42c2c07000e402c58051f000f003d9441131054450100b1101d045003404801c4004138040608441c0020b0a00b9802503141d09485000e940710310030300245c181d0443d4603a419124504440c1c0042c10650414030210003600f0f40800d00d03c2d00318404900c154108402480f90f039440d0382620703849015150680306 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 167457293 1250 167456043 167456053
    0x70501020f03121003062307030603170315090c0901080603030a0207050d1401050106030905010b01020109050c011803050613140a080910120f0f0b010203040e041b121b05090702 78
    0x1803220f81c5070942c0c00414003d601a080368136500c0e59001c444a41520b502d0107030701d000c1110080804070030784a50105541c10b00b007180c24915150b8001241140309260400000040011030030440008040801200602110303100d24101c41d140080e40d10004220b408901d1400003c1c00510b40001110140c0da000e038080c0c00ea0368030323080034400105000c0d02c0c215601c0900d41000511202d091145900808060b603000c51a04070f64144582161010343d4054110390509140101003280068440200c01382031a00441c0031700b440364074210001c000e4000515070b002e00e0003400f805d00c1d200ca04884110740a40d200310310140c58080c0c060364074541090014441e4409100b800350340d2074502850005051141400c480118180d0600411640f07441640100c4940d5441400300a984078410a4080d440a00040d071031301c4c1c2442083c02e41180c000300001c20b41c42800c618440042d00d041c0004c0b0050203900f00303500218059180400456003030034007100314285800c0c40029540744c10010203009882c55000b0300 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 167458543 1250 167457293 167457307
    0x6040f06210203031c060609060f0921060905060609010806010e060f06040302100c051b0105030103060e01140403030f23070e01230304110102010c120911060301080f070501020f03 79
    0x189020251401aa4140805c5c40715401240e000c4420030b904a01070a0005034880c144140036042190356080642040200e880300c90b40b4a81103141c00b01030758001141114100801d40010561954028000b0515410401303004200140000e0450164204440c2c0e0716550783c0394910304d9500c003024402e4403448240c00c40070901600300498101c40700d61000d4031491600b0740f00d070040780006000c0d40e11100012a002c0c1001c0c280001882181e80da00400304051800c902c0e00000200580130602004e44107660754081d030758803c03809502c642d03100035080003080054600790030040c00400c51600080030311407d1210b1000c4040700e4100440b8a441c202c1091001030b203408204a07035404441c0d1181b030502482111503d075003007169002980801070904000d580e450540303015080e41740c2500c400c40c156810188030310030b01d0b07030400c5c02844410381012000881800301e080910750706a0140b401034000600000101b0000303c0400e00100e0b2480203012100c50742e40d500012030b070310348800c88201d00780c1e00184105 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 167459793 1250 167458543 167458589
    0x16151113050f0603040b070c0c080a0201020607030213031b15080703060b0301030c0b1309060909030e0306011d15090106110606030706120b12030d1b0f020d1407050d020606040f06 79
    0xc0341d00540c4a02e0024008e84003961000c0c00041c00b034210002039071001900c8403c560f410000300d613000d041442c080d81024400d00c01180c00c00b905020051407900e0051518003220300c0100c003100180180c0c0d800c05041890043e010341001801e5508100081c2402c0e40400c5107201101164100c0e039114040303146180c503081c69003016811010300c1a81000d90044000360302d848500800001c1c10348440d00040a041070714000d010360341c20001140c044e8100000400c10380c58611503682c0c020041410400c90b40e40c8184d10081000031040c92035522426480000c07802991054603151001d84503030032584a070311150105aa115528420f01000650102158509100c26000024180c3d4041c10800351074015a84840c1960072040804400907550469261000711201140c0c0c0000d46c1c1e410550081062104025100c1c03600716030b00302c00e00004c050300301045109101207400140c0c00c81e0950701c0103254290001d4403041c06442e003512450901c1c0e50591280c45034403404046600d0460004a4031208040c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 167461043 1250 167459793 167459813
    0xb0306180d0804051c05070c090204140306040b010618080607020303040209010603020c100c050d06030b0a05060109180228081006020c0f0d05070b0d060906091116151113050f060304 80
    0x70305c20007000348a000005020480080090702000101680b201d0030104d1507102822444520b81c8658017440c18400403404882c403040c107480c4140b42002c280c0c9130001d0541c035440f01d2540b110509125041c1080040f550100c06140100e1007240c0c440090b0340e03110001c4059015000401940c2d4004900100000e20541d0240841c00704a04000b4100b01050324002d0407135210754002d44145c15440d04006014480c1c1c82138990160702420142da100e4140741d10907135013400c00004905640c1c0d00140740c014aa450700b21003059083c0c504001e082c000c851020003403c0d1402560703034030701d41078050390082081800480c09400741e91024042c0021640864108201d104600d14113948a000b440c00c00314200c041d040c01021550104100890201d242c01162011264245e101061300c070310742000e829004c0c11038806c96500c0103030b41072046685a228141340c40c610032040380b800c0303950f45400006003186001c1d0000d4544112501d9900c6807084da200148001e041c864820b0790b500c0101080014005801480 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 167462293 1250 167461043 167461093
    0x200906010327020102240a0c081003140a02040e011b030c2106090c2d2f06090c1513061416140d03060f1203030b0306180d080405 57
    0x41112424031407251800d04200d0655500180d240d281802c01c901c00c151f50107540803500c2540340c0108146802600381e00150901d000c000c02c43d01c91019000304a08c01040703000e1794250020801c008080150013254028818402c09005000d50101c0003410640244910500303c1016110301c96108a01c184a10242d001d4421107a10140d4400000c240c070a0300c0d215203140da142e03c0c1c43d4403c41c0300d00303408070354424508030007151070820440c900016425844030b04605001c2295007603100562021500a050359500b4019003145d1003940c00308818107034005019200801e09880d04407044940421450151040c541070b507161540c088000c101180c403d406554450203151a04e81c201090410030941800e2210b90945101c1c2011045030901202070107105000110783c01e00304615031500c1d001181d02c410611900012030400c1d2801da003070500a4200305207000c401003d4409a20300004492104400340030032004611411042915090059038400c3c0219000f00040140c440078140000e9440c035551 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 167463543 1250 167462293 167462297
    0x6060904020c01061e08010507020703120302090904150e0604050d0f021f0203070e0603040c060e04111c0506060c0606040c05090612010e090c0604090504020d2009060103270201 78
    0x815119181c003803164101174003060130540c0100d14100c003142d0007000c0702d80141d10f0136403400e0144617070f55400040300811240d00c85158004800d684005600070301035070004d0341e00005040200020804681c400300340c0341d82400b038200035030807141402659406c01142c00070119440440350710350f9503000740120070b0008100c0c07044480c88200703940040d2024030309040b000d11194004c428072010035002292940c00440a803480f03421450140c07a40e80c10039000e031054100748170661855502a071241d0308280b003481003c100381c0b541c0310b4403e2160018001045448040c0074a050b0100c0e40742c0c80c100d021220001080310040c8003907120001008024240c90740c404003030081c02c004900154803143c020b40700040c62031785420390300e40c03500d804841213000040103502c007a0840304060420380d031f0380410fa405a0700002d800080c1561140702049040d210404083c080c0500d249507e81a0400d0b48902e0340c4680d0160740202c2ca03070f00d4140054042c1d030103491819240080302404c070031100c3c1c041c1c5080c6c03c0300c034014 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 167464793 1250 167463543 167463547
    0x6010e06030f150f0609040312050a0b04020a020715050406170709030b040b0f09030307050703030f0603060207051f38190f0b030103081b010603050d0503070320030606090402 77
    0x411403840c6828040250480e02a8034201003141c02031080104030340c808004c0c4c030741040c1b5140c5035070010549017030740030110401a985d20110f201800340b9400004200000b900071582d8001402000c2c0d60341c0e2080c4100a510160410200708603840740094030101c8065484410403120702e14841388040d44000c3c019820860340741c400002250958641c28003a9006000201d402e0070020401d100c120700051080c10550310030018001069130200460f00403540500d000610ba29a00115501034a00c903403000d8090f50020880800303002002c21038203440c0c034000f05041c07022400001c040082c0e80540e4801c1c92142d0380942c94214009004c0c020030051b10380314019143c03c0c0b0b000400101041070300c07140001a161030a000303201401805110b80084c000b1070076450300715807441c0d48800d03ca00c0b80c130b4841e43d00c4000c905410311000380250041c0380955807100c03c0d00c4a40c5900d180080080d042291802c0000307013002c05903c1c0c900421200c0b188052070039510340c0d203103541d1981840301541c0b014030740682299003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 167466043 1250 167464793 167464813
    0x51c05010906020304020306090d050d230108070e0f01151412010b0409060506090a090c140d02120703090b0601030203071101060b030a0b0a06020a15020417010605030d02030c06010e0603 82
    0x2071240392102031040303100503160300341401454584400240021050380c86034402403000745d0810107407284581030030004262019a03255501721120401c0c0105000045c26001040c601c401160002c10744844c070b40041c00700d03034034021200c468110a10816403446070005003000300c103102d20b18000c0c0043d6403201c402c0c5456000001c00f003c091007680b040f0303117107000800c00340010300d80f0b07005220080004403511814800c01200251301140f0a1180c030307201603521140010304034050103428038915008280c00c1e0b19070440d0b8045002035405407040000030140c020000c0c0c031060082c0b1485038015080541c1803417540c1c072800190000d600250100c0180700c1c4520010034500824081e15000c1c01c0030000c1d1a85130b00300001e034842510380d4050454030942c2c400030140480c50740000c100d41c07a26004604000190725940440009100d07a4211402c000310300111500a4481504003070100c5006600721a20840040001c036103d0080c0029981603800c801c004002c040088005540c010b4401002d88030b100d10 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 167467293 1250 167466043 167466053
    0x70f030e030a0c020f030c09160912030c0204110a020a1416081006270b13050a1b0503010b0405041a04051303090f141002010b030118020301060b04050604051c 70
    0x1110802c00001500040801d0443c20120a045003020302913000b000446030400025030382d0100100040c0c00600040760b01020326100340c0d4050000c021a0316604808189424010030804503400c059005504158820b020004100102e03080260075a0244c100020176940d145000c40d000c00101d4018401c41100c0040500c1c140c000c2c9004004250040030305041120500042d60388590105003c00707494240d82d8086030040c24003080c171b0082e03d0030002c1d4a4074850000b43c4c10311b8810304a1285031746071504004804c200e50b0f200402111031800f03c102ca01180321411a03a512090050036204801848100b12904058001c1c0ea0702501401446e00d2091547c8041000c41c1c1c030071180c0d4403c2a02e0700ca0950107154210403440d01510700c150400100300d0505070024440b0a207200a540102c449021842c43c043c800e5000d0288140c00030002c1c01588002a01c1c1500c420310f001d000c0e4403070352070b0240005520b3302074004c0f5411150041d01329814285094104051402200f030005526490420030100082e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 167468543 1250 167467293 167467297
    0xd02090709081c02011811060d060b030f0708090c0102190804030609050d0f090501021507111606020c010c020306070c02060c1501232101020418020a080915070f030e03 74
    0x40c3c540321403950300c0200380c4002c1c00c4d00c0824084040d080c0b09481d000e408103112210745880c408058840680e02e40c0e403402d845006085070350004000c000c0c08828080c84a05006e0814066502a0741c3c0c04480d849848080c1e840304030310055140960701521451490520b90032180350f0450084001c9400d01e5a20788503176040e2404010101c0c1d0541206d03589440c0d20f5007113800c0e810703484120f00e0030a0b945814800041d5036804016410a18410a40c0008036914805c4083c250b158a20740242c45540c124101044901e0400e4007441c00540501c13000145039503c214001003107213030001c00030a0240c480d00b0059990518403041a40c100c44200410b40d806039003044a415140c01c100c01000340b40d07160150315807014483c81d242c03c4035994070b50340c29030043e511001026246100e42e000c1c0c9030a03440f0480725500901c11607100030088140504641d112000507800ba10704013003192134001040c0e030f07800100341d261780a1003400c001d034410300b0700860714840c800c211600b141249400c00050444021044614507 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 167469793 1250 167468543 167468563
    0xa080c0a031e02120a020307120807170c1005011503022d1303030801030b10080606012708060103021c02010804060e011d1e070605310617060f0d0209070908 69
    0xc0d48038041c0c96085045c1023240c01c00804041c0c1d07412400500301e954403443c5105025011386200080d4011000a1005604a8a008522400b103803c0d81d28080700d000040c00d002d1050710410600c6040e401044d81c003e000705c074050800c10f8510700c88441c100403400b2010501d0050110802400d20007030614181604801d000385019032a125141c0d8958070300b5441140e00181500d00819412004200c0a100040c0c82500b103802404c1211408002c800341030360031080f0220b00f61704022405800280c1d8075010a803203058074001d4403030722000015078100c64111174a0b044024009034207400084c02254181e44010b00e07144018001060090309881c40d000007404200400005401042c40081c551000c4200c44101c038002502600703056103055006040e5004001c062000c0200c100501910011141c0d0345035104407103400c1046010b40c5402c0000c21b4a400712910140c42551240802c8c554504504000c002003001000d101444181c0c4c0d0900c540280050720020a01203024070201d51250107106240700 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 167471043 1250 167469793 167469829
    0x70b1806030906090c0d03050313050c0301021801020106140a061b0206030403030c0f020105160507081c0608100e0c060d0207230712020a0614040b03090106050a080c0a031e02 77
    0x140741080700d90309043c0300900c1c8405c3d108440305204100080d82000640758408002170641450141c6070030b100741003d454070000c517855480003070543c04007003090b030040d5404202a402040801c0d201c800310482801d00600c0d4175130040c64000c0401205201301a46020800d81c412100300065855001c1040340c1c00c2070320101e011075120380020310811f03400303011090240c0d418402401785051170035460030300c01e12200841c410400001809001e0042d488225052000c0708203004000da0902018100248078502890109014804030400107601901808241080700780c06810101840740400401d503001c10060304c1050780034040314010561102c043e1005910300301c2d00e4101403038212455410602550090411000751980c00c5d40542c031100081400d480c0f442c20006110395185480310054010f5a00581e29503e0010802c068181306411040c02c407042074410318542c54a80c00d0300c07511856101700e400d812050800c1e042010403050030500c440881103d4011156800580200301c00c204038000d4294 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 167472293 1250 167471043 167471053
    0x41e2c1b1f02061605120403030f020c0601030b0105011103040609060e01090b0304050a02040f0606090315141305070b030106050d0906020d090309050310020316032d051512070b18060309 82
    0x1c45008032416540e22440d281c6081c0f4948244c0c1e200b400c22130f03031011f8030213401c069840e420322048007190350403141c18080000484002d981c1d04d103404611072030309000e010f001400d4200c051521803000825202581c0054a41400035030800c03200315280f400410310f01d4100950301d1400140c668505000f180124028005002411098014402944c2c1d0b2089009040e500e4113008001d10760b03004d90050181ca502440f801040f0142145141c09882c02c0100490619444024404640c050204906810340300e0790030303203402e65601c1c410009980801d20801d00480d0040041e4040880b566100e152114403915005082c2502103900c90103e4243c0a001c50200e402906d09000d02d00d4204901e800b03070305139808250716503e0140042a000074144100c0010315844042a550000c070306c101c11100c445160043c01d55060350011000c02a15041e00c160280c00054120011a41007034103d80720704c0100d820091a500380740460078682c0e680308040280891188441210496440b08000e40c048c55103000105 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 167473543 1250 167472293 167472301
    0x120a02030a0809160e151203030403030e06161808010e0304080c09150d080702040c120c110705010507060204090501060207030b010918060b041e2c1b1f0206 69
    0x5070649002914403400c030b078407440c105001440308084c14402c0d1505164003540646585009100b80c2850340e40641d13000c041c2c1a0b8042060000101a40c8998000d07641800700c02d460386d100c50b403111000c0e00c004101c0d54003079514800ca10b00806c400600c0010000341d03500030a54840000d0700b112000c00e1940034540002504018807101048210b124100c00c0314034811a05048101c69400090107070114040c680c603400d02411720082005607440241c003d80203200fa0f0a070254020188842e0941c8040503500e041c1400308854860ba54540300f0140c91001031100740d040c81c1c01920181c014200c05c55119400b000085400314042c09414003c00041d00104007490462520440c82c880581006480a241800303144480303400220ba00d4040c0e03004000040c03103401c0180410003628004580d20401a006404023100c1c24250b0700000640701000d11801864200e03030610304180d01034603403001c1d090307101040084c402c0d104070200182c403513002498581328041c00c2c201811211151f40022000d0b8000708204 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 167474793 1250 167473543 167473547
    0x909101406030c0a0e01090806010905070908030928030f0b0405120c0303070e0f1e040b0402040b0f0a1b05010603051009020102031803071e1502061006030e120a02030a 74
    0x10400c01400300d07581821440c1c141c1d52501c0b2802824001001c01c00300c20300d001400e0740507040a1029243c090251211981c45416850190105481000009a4603103001410034000f00c190b550401c40100724030140d01e50381c410a20185440c0a07503042c1c0181c2c41c500007002905420401c115a4801c0c41e0444181c034250070b0042c101440388000c2030107900200098400c405021045a901100728103140e612282d00401041001c0070924509820540b518440750b00c0d90340b40d581d03506186d035003260107000d04a903401c280000d03402544160740700d0b040240100b0045801101c040c103c80b40d05440c202c1c4212a0000500007101d0000e1001e0383c10b40d656100500a1110511010303d0040d0740000030b001c80107040d40004e5883c0308400341030640e038031281010300895400f880584000d02016074180c0745a103c001441070300706024412210902c0103005080005400442c049202d1a00340d8009010340349000406c0d40580340c0705805803140d00510500450250040d0003810f0100d10035801184c44200110380 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 167476043 1250 167474793 167474819
    0x20d12020d06090b0f010306051507170307021c03060f0302010503040f050618070f03020a12170a1106090604110904060b1e010e03070503061b091215180604120203090910 75
    0x4030361b04250800906100a0b01e80711210003803840d040341081e42d645054200407111001c651007202d1085000410b001301240c1c000b0f41c50039000d03503c0010010b0707101000000d40440300c961291030166006501d040002d5800380010310342c0b0900480000e50800e903280c0d01c00c0c1c20034404a540b0303444078980b1107000e001c0c5042041042c015200d030481000065007140c0000b2046002841100d541480c0314203050100b220380b0380c856410514030b003210354440100d0320018081c0d1140c0400d1001a00c56400040c4d107610340000ca25001e40e41081c0c03a05425030030503082c44440b0800030320540e0303040d03140e02104100d608c5403500d15034910048888001004010400100064200840c0f50b10aa10000f4180071b1660045001900701c040100b5811107c1c1500380681c03030b17902a0b440110b03400035130346000110480020075408091140580300c500b95660300b455040841d450100070400e141e20030f40029000480043d040b110f00e02490040740c1c10300c410000001c400340400c4640090184c00c40700200700c2e060031035003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 167477293 1250 167476043 167476069
    0xb0406090e0919020d0203010b0301110408150f04020409031701090f05010504050f0708091915060f0f030b06010c020d06060905061e041a060a02010e1b01020d12020d06090b 76
    0x1074550050b100d400c0c1c5980b2501d118020303100d005c1d10350076441155025403144100280190082c04109603118170556250424810801a0700864101131450b104d81c00c001d6106810590007910141c2702c0d602408010700c40310404500f84480c0c45502a4080c491019180c000d0903080b1000c11030300e40c81700841058a0041e80454001d90600051104c0380d580c95860f035a1000907840c150100755102c00d080f500d440780014040c0180500e4140705014000d800480e0090a00000c0d0180030380e035074545842d03138100a41c3c0f048095802d8203a2003800000c0888213440e17001a0140b5240d8403195954000403884445441c044440da5500d20040000003081d00031030750b000703408030b82c01d00d22030b1200110304000e640042e0015204565406500340701012454444100e02d001602c0c00d6215030000602034003d1400d030150301528443e000354115420a02c007558002c0f60701c180e010b803011403a02c00b410b80d4080304034140c04800303035000d2100e068080200d1091000425240750041001c943d030f40284120049030391 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 167478543 1250 167477293 167477311
    0x1818070b0306010320030a090c120818191a09040e011a040b0105070f05030d020c0a0506010b0f1c200409050c040f060c05030702061801080711060c0703090b0406090e 73
    0x48040c5d400c3c00d188019a07500410101001c900e000c120700d40303241c0400c0140c0040008039203031380c2400180072041002d04040390754030012607034084008041041070092103800d403968039041001401810305401d0b0700000e00440b40002400c00c40604005000c3d6215468800340c00c2e13644007c61b051400c3d01941b9a4200d440c20b840421458809100080082c400d2400242203140600a01d4040000400440303030f6004480e031045450350800a503503034480005400070780301440741d03000101d2041910710071546200c0a034511a8641224854960343d82019031021182103079580030341c410701950b004444d860b9952101901950790703003000c8500d802c460f0040e01166aa0100340001c2c00b4284080c4d44420640d24503013400c01d0385242c1c514260345503100e0a20001c1d00904007040c0300340c1c404100108094074801c240c86210300e55840020460b0196039000c10b141140c2d010742d0101d0b41d0140703050020020980280781030004030340c841407410728a41c840e034016400030740a00c1c020800c4410069260750805602 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 167479793 1250 167478543 167478581
    0x12210819060b0301061b0b0c070b0106090b030604050a0e1509120702100309051603060203070f02010507020601061b0203010e030a02060c1c0b04020405090a0903020d0c021818070b03060103 83
    0x540000322a01050080d14140000514008550041c51b6007080301c1590020b03005516180c4125808015000301c2030445801410310000700c0c48601411018040e01d0140302c0d86410b5a550300c0803c400303008003074006c10503581c3d40c40b501e040c200d1050100829961854070b50782c00038204038810b030f480c6c080040c140c01c601001c28411440140d8903410601201c01e820325010405180c5810100d00701000c4404e4540030300014a000000c2200a80240d44a180c903a00c482c81076440c89207080e800da42c411603900006800244c0140203503405020580742101240c1000c580c44d9030b50b039004c03908564110050303603c00c0d40007282030409a40d04000381603201c064220450b0500130070780700244411405c074981c40211511010040d8182c0c544c3c2d41a03c0060400070911030f42803c0c610160002040719881c160010b00071078003c0103142d0f008068940c0b00035400f0b003502017600c281500e8410420030141640c0603003100c0c5040e0781c100794020400d01c0c01501740d40c40d2282d640d0400d00d0024003191b00c1210060208128 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 167481043 1250 167479793 167479799
    0xb010906031103061e060712030f020a0e1210021201091104060c080d090c030f170415050f09190806060a1d04031110020d1505030303011221081906 65
    0x2660150ba800c4801512110026801c61521500c0c0000c00045290800c0000c14640240041c0d2583c20950023595203041105400745800d10050780b08040c0c01c107001c50890720002070181018802c03204402d00c03140a41c1c184119010034038080e60b02230008030001000040050180c2030b0a817190b20804406124020f240c03a14010003d0f00d00c0f460040c0c06840200702050910144200c1d0700700e180440d500044080d016900e030324186900840b80340081d21000800e43d80d60b80074402e258102d0341610784d41d40c0542840440c1500450700f035804080c080030001c0040c0200051615441c000c21a4400398a5800654034100724010b85080b0380280071078450f41c1d016504028101030001440d14561b08003c8100d025515401d09861160402c0c255031124801c1c200004100300507a03001e0280154800c409221203d40000350805a01c0c5a00076640d068004100400074030308640c4608010601c0b608035a20b07803032120310b840305101d00c5c0e900c030400101307200d00200308d030030010003032001c00c602c030580410400642 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 167482293 1250 167481043 167481071
    0x3010209010f050d0608060106050c010509010b0618010c0f08091003020f0d091406090d0306170c100c06050702100e03120c0a090b0d020405040c140706020d0b10030b01090603 77
    0x100c903201c0d0400f03100c4002600f5140100c26006030001e404c2e00d40480d500c550f92440002c0c003d9100310300c107018551810000c1003030b058041c0601202e443d001072071a8180401c4060f500c80c44801f0300351060500141440d00000118403188511425002d01396032a22241c215060183d009400c211845c05c05104000d200082041c0405850740c401c40701078001607400c4075142030700715114203641e041ca00c1e105800c02c11072000700020b11181c10780106d40e030a000c5150b8604a84000c0b5004010b110100c4d0444900d204160404c181d840e4560300d86460900b0034403102d0703200c0c030048031015100c01e030050704003c054040c584014001c0d0b04003004000c00075441c0142c80c841030440100c002e440a69211310000d45e034420540705008010242c00c58bc104243d45541440380f4400941c072501c24140503a0a1400c06039015005002068240300802544c80c94424213a491303070000d61000b091408110380d41c00c007aa1f160345409400380e10040030340d240024004110000074046031400d600c144201030410344166402c0e4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 167483543 1250 167482293 167482307
    0x7020a080f03060a0b0d05090f030703020a17040b0f03060a060903120c020303091806031207030207120201051b0c090f0606090105090406050301090b0703050106031802060a090e010909020a050301020901 89
    0x407440e060584944034400021889543c03507210602c0b004011480031b000b1030241e4032590003407210104650120140e81c40d181e0b1640100c3d14054056040040e228010900120448202a2580030041d14054076103010036190b0300a150036030900c48000c000c01c6a1410805203200290a1031704080b622a403850780c03517040d44050f032039021302042800380318002107440400544e0480728004240e00381c03046101c2412020b070701c811a0514424840c007204490790300c9406040701c2c5029090341c042e01c6010705061041614500c0080200c0c10081c0401822449540c00303032909801c1c00107070740600901e8035400104a50000080e101520030141030050240d50380d14542220108482070038016105c00078035000400400e4542d03c2590103500700482c0b80300b004000285248140792075202000300b66200d8208504841072080e001d41f101c1600780107940980b070404041d10300070400d480c00150b003541b600920350554a081e40006285030b1501008003c40c03070320103914005440c040d03000f103003858420f0000038005 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 167484793 1250 167483543 167483557
    0x32104080d092403110301090e07121a09120414040b040b0609010c020103020405030601060c030219030c030804062c150c04030807020a090212040b0601030c080637050907020a08 78
    0x28038100250344503d0b00135045525010100f903900c5482c0d40c0d44800900c0a461300401c100c1e550b010f61035010985101e54040000170799004440d00410780300801d1113818100c800351090702c4d0751141e60610509081440001d001800c02138060381464800d46061000783c80950808611a41c14540c8400c031945130801039941c0c035082482c0001d01410f85000680003031103150000c0d9098000e503800894090703040b074030704024544aa8220343d519074290071440729520502c1c000500190780c140460300464420220a50468040c000002ea51044584040c41c008030149081e0030307a00c4240d00f4808800003c1c0f1070a207048110621140301890a01d141c8103082c411800011325040d40840d1580a44d101da41640010f401048400c560360456040d020803510804c9a040b6039a040d504c000aa030703540300c0e0080c45084102c0341c0f0740c3e11302a2689800c002c99450707032501c03003d021144980c0069104100041e0400075085440489648a0406052004102d002440081503501040c0c4540c001800ca800301c661b4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 167486043 1250 167484793 167484839
    0x10911030604320a06051006091401030504060b040c020a050f010603110907020a08070501020d0f020a050901120e0d17011d01090e0309041a090123090402032104080d09 74
    0x19000c20101c0341903181a043e031520451154040803010040103074066402803241003200618569030b04002c03906180345004203c030701400e83d00e02c01a694042e41043c5e800c07521030300d8085100c16220002c602225040001c00c1e006a00807084c0009010b01405400c0011210000a02c00e05080da103c40f80000641c9850758055401c10001a85040c400e11908100ba0341c00000a9a00c28040c01d107140030b13400c51020309010529014407030301c181c0105d1080b0781c490321190b00d0f103506094101005454001c520f000004045885406140c075103031051054079420800358440c0d900804800c185101c202205802001d800101d0014058810200c0d42d070381411135480800210b010820088040d055000e201d43c0300d07400a0900d001685514103000142c0010700060300c400760141c1e6140c2800002800180c03044a05104600c1403001ca0300300504800c0d4001d00240494400b0501e40c4005445d00c018407604000004000c101400b82c8d0703205015000d400d4005141c0504001e0030110040d210f07980e80f102c1492 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 167487293 1250 167486043 167486093
    0xa0f1b02120a0204330e0a15170106080f0a020306041415160e03010902091902040b03070206040209070e03120c012004061211040510091502010911030604 68
    0xa0800d80400c00c02e070480d94064000d0103080354403071042d20040c03044510311141d0440d1400001004c00f50441d00301c110780003044c4400c110380310132240c40000c1800d04844d128000c044100811240e10010042c1031440c10b80f000051002c2c030300312000e0f08280d200002c80c03a8035002204020090703500043d400b60020382290320450791034201c105080c0341465107004100200440d070100030b03400b0314412180c1910181030f241d8030014800745041608039041d204000354000d10200c007080008604c5034608030221180301005142c5611401d0503160380d002242c4140050b0701543c01c000c11030030075400007500b00402d4101640500440d00000b5180d000c0f11140a01301d240214580200030000d40050300d10076082140f02c0300340d82622102d9130066010340108000700c0c21829070b2080c10441c920601c9403501071f8212640c1441d0a1200304004000807036002c2041041104000c51145003840a161030b9a01c1500005600701e102c0ca884004540d410060b01d101c1c0c0c005130700300300205e40740306a406890700200203684 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 167488543 1250 167487293 167487319
    0x90302030d0f063506160e04150e0601020c030a060606200303040816021008010302012a0210020705090a090b0601051908091c1101050c090d0b0411150a0f1b02 70
    0x180c0031313411442846591040109010601c03142210b2070800c2690b43e40c130b000c000d00343d0800303000c01d4401c060b45940400b071000d64104000441000c003503802210500c1030390b13000c06850b40040d1400840711b10079110035640e03a504200d150b40194039080c0c401d0031201c4584180f482c11126075243d000060021380403000005841810170001c520f45c88019500510880070340001d9203000704454000d0008038085022180c0225140441400c005405540c071080040035181c0ea50901450410505846083d8841d01c200400c05640d00d08085109250a220020301c48200d810084c0a40c40058106d5040c864200320102e03440c0c18116031880e900881d400d240d591611030319043c0d8a4074010711003a003011b02e03000d45a01c2c11954403ca054172100e050030020f0005440300000324405108102d240c41c2d0003104186690001035800175110b81c02800741c190302200e9074004000ca4140303080c02d2501007d40c24002a9800c8040c0c010080e102000b00a1a15040d0800940a84125030b84004806881844c00045036 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 167489793 1250 167488543 167488619
    0x50d080a060302040f0209040b0402270d05030c0a03090e0105060906070507050a080307020306090f1e030405090c04030201110105010302060d022805071202060f0114010c06090302030d0f06 83
    0x1070010756014108105406640300391400940114480f248140c0c14248615940d213000e00a071140441d032200741d9141004000c001441000070041d005e43c115241e4240c500100d80c090014241464214014042820320380c50000c00d1768156404c40d245500700c5000500180e04c40d90140d400403801520a43d6030b40d240d40c1051458009203900056114480e802d0214443d0000b001038030102e8803c1d011201702d0307100c0c0c203109603c1e0306244000011992044101c440000d07103500c0c0c8802c00007842800d4a25081e00d81c2c001c6501c0500441c4d401400701c400140c10011540e0200803143c014400e240208100c0d41568001400c1d481074400e0076914a40100b402080740700406d220741540182c1e01404401d40642d07000142c0541c000340f5054480120080484a08074004109540314072951051008260f0800f01e000d1462031440c80141d04000ea10207200380060b02900c0390081003400b9400540d100c5480f58400e00c26101c100e449800c4207400c104081040c0756103580d50945080405850712203550319400c86c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 167491043 1250 167489793 167489801
    0x1704080315010c020a030c0f08010509030904151203050a1205060f01050906040506071a0903040303082706180705030106030314070503090d0f02030706050a0804030c02060d090615080a050d080a 85
    0x203580844540800070407c40750101700011101c0c44111444102d83d502021401c9030002c8500018942003042070403050302e865802030341601003d20034064882c0e194024800500c0024000714045080010600c1281d900552b01600d81c04000e5424002d6161140201c0d1041d113003d1011070506c680031404070f00030303a255825a0054900a00119111801414501d09600000981210280025021400f440404412201078a0301500c0309440b035142c002e03507010340740c4401c0790590740c0c400c0802020310035180a12146006400d9a0310132700c041c17801e280c0d419040c841c09a0069119a00d4420108002500b02c014840006070b5aa02c850f12088682401421442100c8101e94000c0310004030300d0400032401500f4200c240254112980c19032144010f40f0248030781503e02c0081a400f0300000c000030700c64910341d20054405403803642094444070341c81003034030100182141c031031351211060a404004048058020410382c0c0042020313100c0c80d00c03640d880f8101c04810f0800c0002c0c420001d00c10004e5504 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 167492293 1250 167491043 167491067
    0xc0d080405010609150f0e01030203030412080f0304060209040b0102010501050a0915081f060b130b07050a0818030609300408030f12070e0307061d0301021801170408031501 76
    0x8000d0010170018881c95200550764013490f03c02080c51031003c00d0300108030310b0f56816654094020343c070700fa0030100010000c0140030401c654034030082103903905d50001d180255000300d00c07609016803245442001c00c0b065075a0300507180d046a140800402195560380312000403078000304400140416001e41141d41000e1541000340b49100300c00440f0307840581c2c8903502840b82c0340003008000c85d07071311519440c07a284194104407000c1c40100c1003d110a102c0b080082c0a02c0d40f10f1821124042660f0f0782c1c400307290704404018040c0c510a0f8103103001e40c0c10103000481c2d0000c4013a01030300020b044035848801130790b240c519011001800009030301c100b84819044402800a4108480d01e400d03854211400681c040b44000700ba1a03800d0001c07603003803400340140c600001402000707080401e0600c2800c0f510307034054003100b81c0f00115030f0b04458241c0c1c4003031008140c98400c0c0300411500c4a040c1d4005804082c034040c2544003120840c2c20400400c901e501607a800003443d60011a9003031000004843c143e54a130 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 167493543 1250 167492293 167492309
    0x4050c0a08010b04060f0f030b0a09020d060501090503060408071406102103020c040203070203040e010e0a06080307080322060e0717030c1f110415080c0c0d0804050106 74
    0x442448011100200501115880c59480c00c181e40c0e00d8140c1100a0700443c8a500c0c0465010150f00c42040c0c041c00a03135940b145203140c00518004031000060102805a100500b040d90002ea00300503040b0307901032000542003c0c2001c4a216103054042540c0d82030041018145280204100b404c0084080388804000b0300c2004640c658248414081c1d40e1900602c124880c511441e4444001c0451455030401102d416070050226101c0c014144006540020f091100f180001c0202003200d001c1c0030748643c0a040795801070100f44c9007a80f10101141c4498110303492991041c400340000a0101c4222a88444000081448014010404017980c01070f040010807141c1460780b51a25480005080000c0350090103043c43d101c04036001c80c0351a84500000c12200b9000055644d0102540c0c0d40f02c00181442079000242c0700380602d0601f80c507600990072401900102c00036417044140d2040c142034022082000c180d01e00404d010141ba900d40070003400d0014054083c0005041c46400e42c0600300a064103 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 167494793 1250 167493543 167493551
    0x1a0609030712051f0c022b03110408010f0209120304120f051f021206060408030a080907090c0c0c050f0904060507030e0102041202030f2404050703060c17060405060f130b04 76
    0x1000300600a0580d004c1400014419011301f01840c0d00401a01c0d40d01d00348041f402401154140022005843d150850b0400c05100b000b0020701c04009101d614500e0300818801030b00c80c9507040c10001c401c6c9007026010400d50041c40180141491030a583c1c5d08154065404a402e03103c1c0d180035802c24003041204850041140c600001d201c0f4141c00038080c200030058025078660303d080070040f8501550240d5000e5510502004603401e011b800c1a5401080319421a00c0d05582c4045c0c07030782503d407412326190020b00c98041003400c20998400342000f41c4402c58100341c500401d82d0104234181802040035005a40310808258620b002c0d0f8401d04034459070380001c0d5901c90300e0302c001d0988445060802c074081d210303a1600d28194540850000078100380c01000258112030b80440340c060540c050010781d4140100780300080010054480c4401c2000c4540390802d07407107000d52440e03d800c41c2c01001107000f64201001c1214542d15040c10781c600d03600845071031030500c201012040060071010203850304280b43c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 167496043 1250 167494793 167494843
    0x60a090503060f090d0f0807120902030321070804080a0e0103090b0c040812121305031b061005030a030c03050d02040b04170105090a03090e0712020a031a060903071205 74
    0x3030307483d0040c45a8503160407600324041c2114202c80d0110340844410021b0084000b00e503800d0f10030000c45142551445011440c0c07051a00003d007954400d80e804d003051a401617080d500e81c0d0001c5076140d405442410542c4944c64a500c07407903070600c00c0900003405c10820f402c0060840e8042e13403058541540103610040740386810944520a5402406481070501c83e9201000c85071950b0011604030421800c04007500341c4490015010102064008031000d020910a04c13203041c5d030b01299581440c0b07440c0002c0005051130480701211031926040540650004050318000ca03070068950740c4801c2d410b1030010341d030b03401c220540c800034060f94200805408000800245441c10a00c4c0180818030280003000192200000c0d103070b90f80a050001000b0541100b02000241124440203a04c6103407801c095403c0c0100f143e103541240c0c00460200e012075039035500f00c0d64084c0014400c80364160140c59551401c6000300000b0b90b01c2c1c0103131149030900d80151605071308000050040b902600403601d0b550200100d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 167497293 1250 167496043 167496061
    0x6022803090e090f010b0d080702040903030207020603091c091d070e0a03110f0a080604080a0507060507030515030d121d0703033506090a0b120307031e020705060a09050306 76
    0x4001011302250b50309041c0316021a192544090302d01550044120b0300d400c485509020251608450581c18541d00b070040c400542c890000461069080c0b00c040d01603503031006409046a801c180c03001c0100700d0384150602915a02000f008011003005078180c4c15541c58a030103d4040c9100000342d40c00049440002040180c82d6041a00c0311504542107000c01c03001d0014410b03102442d2141607084d40c851000304000c60344036001410740a0580c1303409031811180391241d4050b908160f50500029503260104040c207114460207107000308040340540521140c2200090864002407007030642d541d501c0c1849a18031190701910a01e031035200b01591842980c0e03080160003041c61810100d25050000c0380240800c1005035030050b103010405810801e40c07102014041440c2c0700030602258a42c4da000e01c0303845aa0f541c5503030101104c0c003c006580d24603480c50024841000525461204001c4c0380500700c16517004038502c4191032050f1607281d21452900000c44d010401540311341d426010b68424490200703 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 167498543 1250 167497293 167497303
    0x60409090605090a02030a080c0c060f070501180b0a0c0207080a05030a0f0c0804030303110c100b10170601140403080a0201020d060605120a0e120d020a0906022803090e09 75
    0x24001c260400c0103a40e040c5619807030740401e410080d45030700300481080000c0c0e4200d010340206441e0700c0440c0c2d440072031000481c910b94060b041310083ca00d000b01c1c803402004400d0148085102400e803400340d00c0c908a40c0d40300d010a402504601340da80e10b9131148140a8404c009070002805a002120380f0320905003886510f030792090fa4214001102041640790170341c007880444a440d5809035000e46410701e1600c085000784609040c0c0c0d05da054007000101003070310017009080c001c0d10484030000380d05880702c0304000e00b00010011076814405264600c20b20b600c1d4114055070f01030b4080c01c0a691500a03001c0703001c1c945c802c82d04000e2800c8000301d50b40c40c04542c154007820a88201030320400c4607540f41c00341600c071400380031068040358401400141e1170004ca50429041501c140007220003d1450080194140e0045840f41d080a40d000c1032803210b0947c448000002000240003170030110682410050242c501141c00c4000600607000040415203d00c01c110000e003c10a1680010b0400c440c4490b255 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 167499793 1250 167498543 167498561
    0x4030303060e04150c1e1119020619050702060d0b010905040219030c0201020c070b070b0105040216082203120201060b030c04030f1a010303051e03130f11060409 71
    0x2070700d080d0001ca000e000381480103001e030350825488421a08a442c4400281400b0507a5000f003100080082a400d2a8007240c1c10107030b1300503160b008001d607980000310701d8003d0007660b071401804012261300168071428100c908a4000c00354040024141c02c0054500307200300c40d0000e400510000c3e074454080c20300d41c01501302c2030007640c611840c5a42c82c0100b10503802101c000c5800c0164814002040074000d50003a2005243c0e4000507051110951019040104c1c6a208049041c03000420b402004202103066014102c111030840c02e00c21001c0c2c00480a1010300c0005004000c0003940f14074104c80d11584810050740754009115098413072605550016404c0c14450242d824442d02141d2854003005a9110301c03428040203041529680700e00300155900c0341e0070348500282c07060b5411072440c0600d50a000e503010b0749030b19545651a41041e28080c00910b1420b00003d428002e05c410f48040714200d020300da4021a40e900910000e060102c0002040d0307041951100e0300050006006500303421007852 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 167501043 1250 167499793 167499797
    0x15030108030a020d030908160f060c09090506060705060c0a27051306060f051c0e0618060903070b0406020c010e0d0207080c0315041a10051003021239040303 69
    0x58038400ca43d056095508021700104502030508c240901c4d41d0a070b514100c2c0d41d030b01508001c01d00301080c0d01e0304000c0703605014068000403840d050910090f072081c0038581d0000010f0b140b0f1842c18031070703441e01512007101812005039140000344681031b451080e0500c12400752260b0424104807807080f04d420a10f070076449928000c0c40b1004200c282d40ea41882030804030341240e110111060300c0d0f59001c503529802410b50100300e410052841d01c401444e07201e004215050880106401e08001000741301034008080410801da100c00100942a840442a90f8006a0014160007652aa4544400039020302c0414644562a1440d141136040c4005100440d600040c1c0036107281c2a110000903448100d07100c00f16806921014050500d1000c110109030f025004020369500c08030a4940300d800070740c0030384100c2c2c0900760151080c8901d20340590011808440d50904516090041c000e01c10740800c003c01650b170816600000a4001300d106031106400c2626501c2501c41c081349002c030140340d410a00050780 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 167502293 1250 167501043 167501053
    0x60303040f090c20100e0f060a0b010e09010315050c1908040c050303090a140d05070305030405041112061e0d0b010311060412080313081b010b01030b180615030108030a02 75
    0x20051308039101c04200c141c0c090101e1250410082003d02440054001d0b82e00c580381c403007401044140a09070148050103c0421260b0540000410410382c1001091013050322400400014440c01e405043c02c9210707020100c5d480d56031036661042c60107001e01c0050303c0c51156407c2c208003a4000d100500c5540f00303c20394242c068940081c160b50b8050246c0b5581c0203c00d818051201d40c000e10110303000d4010050400160b01c0c65030361018182591580308840c02d0344082400d0007180341c40d000d00e40c0381c1200c808810307051600c94482009007003005824103016921950b600f601640d00319030201c08100c00032b0f1030941c242c1020301e00500104024481551080394062460f011072504808483c101c414807500301d0440381031521100e00a600160130708228000c940000400180c0c1140580f02c490828800101c01c5419500860300b980c480e131803d070341010310b41201d01480c0da9541c070b1003280c0d1041c3d182401c9010703950400801c2c1a0403c9041a400e490808000012038840020080c072400e4865805e80d8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 167503543 1250 167502293 167502317
    0x30c05063a0207111306050102100b12151501030504030e011209081306020106080105010f0608180d110c0d1502070c09020309010605030d030c05070f1a070e1503060d0b060303040f090c 81
    0x101b100d410340901c0340140c000540020190000d50400d0400c04402010940c107002d01c2c0e5062494840e84200905500d100c0c003082114447d4020740032211680282018001d5103419134000308420100861f41e4140051045040c40001c3c5d181d0151002c0c0c0d901200465580700c10006001c080c8006108450041d800d04101060311503042c06501c1c100d030140815440014106407081d28990401800c3d55040440c200507058811400c0140c2d500600c50750310362124241c6111f550f5410f2980f200c00b1280a100014500ca00082023a44000c45019200000685903520f42c0340035880080b6035030242d00114004014882c0500c0d0660200d01250800c80865000d09000303030b401d4083c3d42d4040d404101103071040c0311040128080880300340e00d00e03105480000e416540c600111180300819031b039030070009800c0310581c14035040424010504515841c5103d040d49031440000c0c950f909440e1000300704460000214641e44c4040081c2c0b070180c140c440070719421a031908040c42c02330070390700c0441300011a021940 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 167504793 1250 167503543 167503579
    0xc09061802041508180d05030f0906040f0305030618040b250503010902090a030206030415181e0f0503030405060907050109140d170706020301030c05063a020711 71
    0x1d904030740300303050101c10380c0c03004410644e5400f100404030603540d0605518210f003150180440c0c1180c1000392500381e00c900b0070000408164200500a1001e80c0c0320701c0c24040803c04441320140b0346941850728079aa07030358410100e82007003a04c040b10aa500070700000c0c0400c00008840c040d114141032260b4081090302c0c1032100401e50040b01a0f24003180e4200014824109a40c00809010f2009400e50b041c95542e80e0120750294400c4070284c515a90500304040303050502d001c0c0138a1001c94800704007a43c0d050740c551b585e1000e1031210303011400103091100000c2202c2074040d403443c00d0300442500d4403440d26050081d1680380481ea40031581c021b5610110b6658018554030003076407038655a0b028145851014042000d40079101680c030b43c006061140c040c1a55000140140c1d8401c82001d0380300e51445c038000c0d00407500b94110314800d010500500e03100501641d07881d0200c0f01c1c0c03034101d462400754103440400101d0031400385940c214000501c000078071644451403008240b081ea5a001e0310118040c00c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 167506043 1250 167504793 167504797
    0x10b03030a08160302070c091b02010501081e19120e030601150c150c030c0e0a0302010804171e0301060e030f030316050405030d0804032003030a09050102070c09061802 74
    0x401d90101c0d6211000c01e06200084030150195066401c0051410035141c81e078000e4082154801c0c01e1240d203d09007030240c002c0c25410918100300c580021300c880d5040c0300c03003181c8480500d07140c1d4501924410320000600400c11074424003514052000c503150300307107042141c3c1041c00071180f0b0011401915480e1094100018854121150a01c080042250400c401c0320340d841c9100017601d0007565143c800b2450841c5100d89903903c0b420791400121410000b001a00704040110a64400d001010702000541d821170b814a6100d0b62082140c0e1800388070b5484a06980a241055000c0c40503254080c01c0c1c1da05c0704001103050383c80b0b94440c0500e860001c41013599a18030a540b001c0a5001400400d40b0900d807900c204030015054240103041c1a03d50f400300f454001a01404e10008a45c0001e110616400ca20605581c501c048a4801488040b00d550360b620b1101400b60444240d80f000307aa814010294184c40703510f0340c440b680c6500b10750b44510b17100c05812103000f14440700d0801c4500034080001842 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 167507293 1250 167506043 167506057
    0x20a050406091413090503281205061003020a0c06060e0a0b030303040201021b0a170304060305090d05070b0406090209100501081e01050405040302031218100e101d07060c05010b0303 80
    0x110100803044407084e404003030a41d245003240d29200c1800681700040840038042401d440280c2209070f00300d50008002d2040580344180c02d140da00e0038060100390384032440501c01c207900c24200541c1c1c490b4005011140150000d00250040d407030310b18041048a410741519004524080781400000c20030300c201900c0e403005a0b00203000d41d001c06121310703803592400c1c00800040c1005041c90f0250780d84020039070a142006031311040c180c000040c01e0000c40e4161042540050707003040140101e98007514098960b220700700001c0c01100c1ca01e0300240030001180c200700c500d294007502459007400d0240c80b04008030550b004150100e40d02d0fa00054030583c1c0e081d149001d10881c0034403903142d0303460001032200404002e0f1064045000800500d0412006115072601030800a40940003041c031101c560b40c1001c0b81d941d51000803d08210b940e58400400040e2029074880113000000c0582c40076003001c002c05501005404580100c00001900541140b29040712a02a00c003c0c41244201030405072030b03209440d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 167508543 1250 167507293 167507299
    0xa1a06090609090a02160501050603010e010c0807210c02032107120e010605040c05040f0e01050a1401021f0605010801120503040303051b030414030f060108061f0504020a0504060914 80
    0x12058100c00e24188040c0c03074200402290051a0070072440104071046c50980080c0c6d03181e9101d8040c05410b060034410501406080030080120900000740109900d0018010904201ca03500d0000d1441b4801d01601845d00a90a0f0800070310f0314000d4080c0d01c036000180791b0a200d51b010314140284910441d8500e2250b4020b41c0d0340c2d6280f03e007a0f00700740001c2c0319020030034070a5961000003043d244c442d03201e80c800700755403030715881e49413032421505001d84000b03038100071511031880d00108403503102e8a01083c240c812001c00d4980c0c2c2000100104e140040d203106c810020201c400802c004200710b40d2240e4182c980a90b5030407011b07038035031128206615400000821a500421040001c41c0c0304c1c1d0081c01e011000c4209203401d00b03840c0c0840c1490340e00a80c0001101c0048100c922071585020010b2110b9401450041c1c103203589020300302511a28002d0800e0f54800c91481040c1402c2c26010030100130b850018821512009005002003182c1c105004e901c2c04140c0815000c544202e04041c1582000702c01 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 167509793 1250 167508543 167508547
    0x8070e10030e030909040c0f060e0d02010806010219320307060207050312090105070306060c0c0608070c0206040b0c0106120822050d050c150c1c020a0b0a1a060906 72
    0xc920210014a12440000ca940c0000c0c03000140743c2d6203040001d80210701400e01d1035400d5040c0b140c20041c0100c03c0c3d124209100008415200780d80b01d408801080030f809090618040e618800142e0a100001d43c03500e0100d120f580c0710908001d11142001400f5904511006903108020110b40c0c41c2101071600d0b00c1c03550310a20848000907081e0700200030b524403c9080c0c5c1c0c00e08c0400b15426560210a65002c281c40c2d440e0b500b00b00b0b0042d4980315150040040d840c00c09506441901c03500d8081c03809001d4079041244600001d0b100900032905d122080794040c010960b43e0350f889018a0707007600002300c100038035402c00303000182c0c410903000c00054a40e0016000762804403a1a0001d1007035415040492059611810010701d640c0d50000b2502030034020700c0500200b2107800d00300690000340070403403546401e00f488909100300d0b00190000d50001d01c03080050300e00b01070304000d0f0300c3d00484940c02451800301d0f030100501c080c030343e8000040f40d0841c0840d020100c0d130743c201041801e010342038a090f0000c40c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 167511043 1250 167509793 167509819
    0x1514090d080f100b0406051c0506090a1a120a0203011802011d042310170a060209030a0b100e0112030f0e0d060f140603070b04050105070507050a03030f08070e 70
    0x2c2600990805070400111071001c0d69920403800d90b030000d41c070890218070301241c10040c00180300e041d44504403107850200080c0c5131501c00580e682c240903010a0046907035141702841220058065600510020300244103005400d640a65a41500004a009508000048907001e20f901100400d013641610390b008040c3d40a042c3c110040411030060380c0c40758803480c100c050411010b042100000000c02203220500e421003441510250a13071011207440c0340b809400c5000c40020501d6001c007603000001603520500000028a0800d0252001c0c081c1043c00d0140a200c4c3c40b142c03548801c80d00e150805100e180e03611101c50810440824002d8085030702901240486441619841c4000400819903070191031591581005c64075880d07000c0303010741da45003580c1c100001e4200ca03a44d071210080300105900c90401078104c5030b80c003d40c41540e041c0040440c0a0003048018007988000e000b02800480c240c0c3ea803410000e29910807804204d01281a40f008540880d11910081c0d401c020050001449000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 167512293 1250 167511043 167511061
    0x1a0301050702150915101e0803041a040e1611160e1806040506010503100b0607060c050c0d0203071e0302060f0702031e0309010c0c05060708131514090d08 68
    0x200100f4040300c5000b116040d1200c0490261518050006081c10a601500701884480300d450707c004040c3c04070441c000200701d11a8004121015a40d01d245210854515100c03140440e000f26007244001c00801020480340014020020000d10b06541e40d445000e181d81c81c0483d00e5562040d406d54414954075010701c1011500000950400190b92034081080544000daa041410035074040700c05801c0800108a41c0c94101f009070407680300302c50100452082e210004105100b103401c0142415200c1c1e52a10119010380c098504d1009414190303030002c440f045000392a17522001040f00ca24903101c02c80000b0b2140c1c00728000085900d40c00030805c2e9124001007082c00f04005181c10118403081001c05403a080354031204600c080c8110032951030303003001d04540342500d0340d5481640401046002204c0411030000300c235904040c050401100c5501d030310148801c2c80340030041c0541004c02410b1100280002680560043c44403200c00b480c1c81e4071003450742900d07a04030710b0500c0d0001d141000820550b003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 167513543 1250 167512293 167512333
    0x60106090e0604110f0a090608060f0102030d110c030403210302090d06052e26031e19050304030905030f070b09041407080a050a0b010f120905101a0301050702 70
    0x1600c851388607030400d20000e02400103070344000703413240015070900020020350390441340c8039810110403200301a1102c07002000070341d00d019a81e907581c3d5654480c1c1c0d038070170800e00c0381e01219807851000d81a259182c0e00c1e4101100c0200d41c121019501300102c0c14190f40c0d6138032078400d440502c60001d10f0807581d101d503a10340801601d40035080a400c03000010307420100300d261840407019480301400c54550300d480d105000e04081307103804611443c1c0051008112075402c000c400c5403c241c40010b401c81881038207601d1181103000319202c05103002040380070101400e070450702443c800c0d4480d85d980d0321000d0b00d640a254688410241c000701381c0d44900c0007480b4800200000e420b0101d00944000344482000380034038a40d05040e28800b01140364142441040340182c040d41e035120030240c40074441c0c1e50014000a00d0019240301c3d00b02041050780b44c040b404d1306c4a8110310382d9a9040021543c40c10500310b28080144021350720604800447c0b03000000a05041c012580300b180e80e6005012900c250031107e500c04 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 167514793 1250 167513543 167513561
    0x1b0e1014100c110603090c0f0409031e09031709040e0d0203091302090603010308220501020c090702010f060b030a0c03060509010b0714070b03100518010303210504050a05060106090e0604 82
    0x10b4192211995294444c03c010f984a00700100040400168050620811a2400c02080d02450411001c00c002c44d4020301164800002414101c032480d0060708101c1d801011a00002c1480e80020641307903d1750380020251140c02421141004600e0705034000c2030760f030a0b211400b500540c005000002d15454060108000403846000c098540300c003c0300012069802600111540200032400b015000d2000710351f83c85180e41c0411104001d0704040010b0f640700300f04200f66118146581c0000c030090300c00e4221640c1003441d40814405240c4440c0001d0181d00121ba0f003600c4180340004898015110b40a03120440310064081c4106909105d038031080c9a204070f400f6a1070b1514a0f1074000c0c4040704004c02001086104038089d02d0703040500803c188064103601041c41046440c00101418035455082411650701d814958046e0704448448244014142c0180000c58a014104000c0c0800401d04ca98070034450410742e241d0303a80310881560004114061074060200c540d0015402e410039610080300 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 167516043 1250 167514793 167514803
    0x3070b010b030c0d0f052706131104090b01030213020a090b030603070b160201030506040603230132090d02060c210a09060506060301120f1b0e1014100c 67
    0x24100c001000f901c1a41d02e1154403032185555041000110213410000406859092000700740d01c1e15030701003280e078810005d40400300107000c464019041044454ad01418801d0140080c040c01c50642031108603590241300c1640204003103034046d0081001031080352400b840c5603d039404481c3c2090740501c1c540c2c100402c01509841080408541100d201000d812811001100c1101c014140d10004007540e06c00307000f142c062800c03c7d200740000740105180c40c050310810b1041c030000a41d00c030f071543d02400803021007990310000c03040000031490420540040e01d801d4000780c0d03460342d210302280c15a905921000d06005801140120b00900b0120006185110030601c00c101d000c0c1c400380b00d980038028199128642155124a42c408102040c0107da600403001c68207a0300f90b42c502081e10200c18100f840c0100f219411028070b20401144a803085004501f402c00020141e44403040c141c1c000d81c00340d4042100c4044840002403031042d89803080484800035202c410826101380043d07511141d90710041794 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 167517293 1250 167516043 167516047
    0x1e15050303070c060f0c0f02040213030c08070305012a050a0306030c0e0103051c020c01051303120309021201090201021f0e0d1e0804021c050f03120106030b0303070b010b030c 77
    0x2509a40400180103124003c404541c412450240c4c054030f1058003400f8031050100e80c0d880000407031030740850980b566070107540244e903c0040052041040c151a040140ba21010800108864500050403c10f4a10800082004040d04a52401400500703074080301400030500c480c030080740c4120040c03c00e0408a040c042600f0745c0b03d0341d8002540d2030300d82003000c07401030b010010000c0c403c042044034035440d141c208403034496075000002500c03082000401414400002410024041070000610065811000389203c01e51980c0c0c00070702a00720340e03405034410a004a03040381510010700c107014800354160018500c803561444030044981000300d10200069490409118081041c0241c480340c002300d40e40d03a03608210640b0b1600e1030000402080041003602820400142c441e800d0ba01599030682180c8240d03550320703240841c6030033703840c180001160001150b05507681800d0424581a209a600c0038040030100301d0500da500d0258010241c0001c800e0001007009010900045821100c06a4014 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 167518543 1250 167517293 167517299
    0xa170705031810050307020d0e011b05010b0406050a210f0609030804020a080102040f09020c010b0a0b07110f060307110f0f03180a030c150c1e0b0603011e15 69
    0x40d086410210184810820b404401019407a105aa0203042007440c2800d6080d801c16640003580c40c0e17000308500c801c1c0500300c20904503581c01101100f59400d40c0303403003a12151080c0d00d03040d40a8174a02c207800d405181041008a03087c03518040c8a0142d420454881c95000c100c00100c2581c02401d40003511902c00c428651008100540600c21885000c1e44440309141894414810680c1c0f159014803c00e03403041c07005020503c3e03010340080841c0c0901d40c0260b01c49404581c01801800217102a41c1d201d480c04600107405980b00002d09445405803e00f01e07074207580c400a010b64641d00d0710800b6444042000050b2456005030204210f50480e202101e046102d6052000e20b808001c00ba04c11107540080341d000b0300481c040c0414081220306032601320640b03142d80e0351421210118003e5090a00c461500d141400d4410248100a6030b000b00388039034021a40b40d40761151140000064415201c3c4000040d994101401048a6400261645103550000e022444020280800c0603008150000000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 167519793 1250 167518543 167518553
    0x1c050712110306190f1206020f2a0601030f0807050a02030714031605010804170d0f0603030305060d02091b07080c0c120a0803011503020d0905030322050a1707 70
    0x1a03030140140300c825503078100f4004005a01c0c0b195a0126103004c48400c003441000500c113540c070100e920300307030295442e00d000e85840c8001c0d0040c4650888851004a294408034184404e001e461240c2100f0156083c4040e400850703d030242400054448052614900c000400083c020b04109025500740d4940103619030010342000e406600156030030201040c01c0000e4034007448021480000007175414078451902001801d44400104041c00e40c60440e501001146070380c00807900030300703100001008070a2850312230382c3c000e2005000645c00286048009902810a5074007541c503160024900c1d42c10703a481e400710544028010600d460040c200b80402800a110034014112140b901c01c050840c152404050104401d480d000c00d02c115800300d581d0901089000003124195213801992413031015413200300b0f6010348100c111141e506440c040b01101030120110265008200c44051002d5030341c12800014102c4001403400703000d0707402240c0787c3d40004030340c2600c0152404030360b00d40e1814070305a0784403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 167521043 1250 167519793 167519801
    0xe03010b0a080d110604021e060d050f07080708250302040e0406020d1413060203061203030702011b050708040902070303090f2010050703030c110106180b0102031c050712 75
    0x80b000c9075501103d601c00c000303900040d0803000010b0500c0100340c1c1d40340c0f0f41c00240c040c030b4007405e1041d54869800c41804454951804440e402501c840052042e800e1068468040041c05c561140024071044089611b05d442004104c0c0180b440d05032a00444646180c049030303061014a032801410b900b0000014510401901e640c0710318018100103854100300981501076451090b40d400c51802c206042001494074040504841900440d005803281e441c80301007000380c08642c440e106c140c40301108000a06605400071481c041d4803205180c5020b80303604058a80e40542840200340e524280814088185580c0c05800603901a180106aa000b84d441d0345020103000041078542c02569075840e0701e010100c104612035500141c0d0140c0b514000040020201d0251610041c10551100040200a03108114810501145070020800755549480c85420184d824010054490074100800481c1d8004410303206080065001078440480c01a48000100300090044042c01400703010a0450001482 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 167522293 1250 167521043 167521049
    0x30f170612160f090605100206010b0c07030b090102090a1514070611040b07030215100506030402040902040e0a17090916020a0804030c14090606090411070b130201080906090d0e03010b0a 82
    0x801103d10604002e10708040d0b817107036001503000c0d00b0044403240350254005032481c11520f01d1344000d03450b45030350300300e450406040341d1002d44844007030070900050f910198020300003050b0440d092822507a40b84c0c84180c01101c2002030038081041c810000141d000c40c2c2001b8a426071043c480003030607015101e002061a00f00790000c000b081000b0406404040c0c0400085034810035010903400d0310324101003e200e1504081c0503c40c0030f141b011000c10300310b40b501d401c1041401d80c003c2050191002401034240d6520700c1074015200e190403010054400c5032000229204030070080c0040059a0710205500b00c180c10701e99840046100d98500c4030f0106414034040d2010b148209405020f0354a041a02c1403c0500201c12034814100304084c0901e0740d50300801c554050800b510041a4104141000d140500800c3c0d0083c0c0401c04500810403554550294804034500c02d8950388116280c012401e036451204450001203607001c10590071040e40242070300c90740781400a0000c1416102030300440c5415490f64 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 167523543 1250 167522293 167522309
    0x6070507080712030206010605090a03020411090a0e0604140f0a09170403060204030308060301050709030b150411030405011407020304030323070b06010e010309020a0306110408030403050604030f17061216 90
    0x83d14070013015418440f42c0e006041c203152a5081424000001c1d050800d50310009200d44e60303e1001e140c2540c444415550b10500080c80c42d130a55540300c0c1074800c000b00c225a005d10440c60801d406035459084400117000301c00709912220305030355200e02c030002803000903003d43c1c048070a00d44ca0109143c8450040c0041c5116000c0581c50b60b14518014080e8400504070b144607905000400c6801a407064180d42180d800550402ea0742c1c941c064000e0f6001d0b4010910340d0098242801c089011644000a50082d41718000030406c19942051400b009082a600003005800030003041000ca886545417040101c0c43d03101201c800060703200d252100781d1100b103045811740400b10402c102581c21440c00c1e0119002800c1c01c0c0702d040c240d80d0001c2c80d942124040205001e036100c0310301181c1417801064a02800804003101d5907141c40e810407039034071030080b0b4007200040c00c000300001c0d031030b031113020325a0310621323200b001b00b0117516038408210b03100caa81114a58240314003008400c0b000d02d03c00c8060010020b01e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 167524793 1250 167523543 167523569
    0x40e0108030a08010504090b041211101a090402060d05060105040b0c0a030206060312040303051606020408070306061413020a0c08040f170f0606090907082a0a060e060705070807 78
    0x344000f4110201c140e0200d88982d1030400302d1804141c80c0c103140c0354001d138060360140f0301040240e4140c1d01000914501ea80c284511003110455000a5002c603003595a00d58462401c4100c95040000e207001c12030740250411814061021051001e8015541000b0141095414181c4860f05560640c0101d440864250322600c0710109054042c066641c02006c1030307014109011000140500c10b12031807000030100300f0002044520841000010a401680514155545e503615400d4503984c0800380415031b105440c000000031510381c4005102c880540c0942644952841504070100940001095509201c0c2080c4000000303401c900040000c2c14034003e82491490800307180303012240c2103500301030043d884040032141b00003000034456486013003210030344926a28510110309188065000090512940c000e40c4076030418040c002c02c0d0030b00166505038404150301c0401841049501c100700116005c10003955150500711300030061180144111420959500600e5281842d160b010510248071 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 167526043 1250 167524793 167524807
    0x5100203180a0803180a0c120507090207110d1a0907061103181012050403020c040e0a03080105040c0c020310061505030405070e070c0b13110a030510020906040e010803 74
    0x200407404480041c00303030001c1071408800e907074240542c0300103409140000201c2405201e104001c2046603419640646201c3d01a030351407180041c00c0d000c07144201d17114058440302040d541418801e0381e8030190045003200f400c02d001428414200510501610499010844480c0003515524100c0c051644840100080343c07607d20014884100000c4594480d0010820b0358102c1c4035140000204510407103010b00e00c146000003e0307443c2c0c119460b601c01503d090400700b106064021030a41180c403c151424410b45002c00e030350b00c0d20b031102c229005010482e10b000600590616a00403541d040340c0c0e0416201900164000034984504180220b07407a80d2074210500c484006142c1a046114031703404c03c9415030810741c0d100354541810b402050440d1120600050044c0c0c0300c3c0e010081c200e5005034560f003135400c01c08260540d10011000980e20900c01c1c0e000984030b42800350409003125080001340280d140513880c5039020b980145042d682c004c40911010860042000086000704004401540d031101 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 167527293 1250 167526043 167526061
    0x610050f1b0a1a0601090303170a020405031506040c050408061501200c0a05090606391c0f052b0e070303030f02030103081204062a02011a0609190305100203 69
    0x3100130310107810045585410000250080a800c40084034444141600d6032880c018000a0069511a9501d48074911281d5005004600c41c00e0054000b56014001440d400c4000c0d00c8621540c032402115030f12000c0094019618581100d040d000149001c000001040619000d900780950641401c3e4100408401c0103140400500c0003d02e8251038801582c030f440070005d0003030b0103604a04059403110301c4803100400000b44940400340101d24407a160842040c61071580e580c0106170290b440002160340c480054041c402c9503141105030782d10fa1307190031000c80c40c031800b03586402100b45011400000c0030039199118003844206454190040c00391500e5400c005055500440601100901c10001840450030035401c80f8a90b2100c0340c003408040e00e55240100051660210035241040350282111180c0d0500c0c03006403920a46900070710440b4000c80f0030800100e03460303002c40d44c000740030450804d0a04050030075885003400c3c50f1028601c0b40e0b59464050a10f000b0801c0c0f250707a80d600004100481c4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 167528543 1250 167527293 167527343
    0xc070e0108060103030e0913060501090603110102011e09020105070803010b12070c050307020409020d060c030e010f0501050d0b071e09230a030b0c071a0406050610050f1b0a 76
    0x714162005101075403450703c0103044610040009406101c0c1c460000348400c1710391030303038004083d03001320100700540c1d580301820024820b90204803048914540002580e62050043e0009101c00ba0b04c006c02e00700c080e602680003006102c40890500106000706404901008055070082a4540b54550f80d14011f05241000060042060042c0308030020780902040c0000b0540c1c4100b54103550000300181c090002421014030b4800007004541400107558100358940c12502c1d5140030b542c001d02c4000c021001382030541c1ea007401103e8018104150b51400702e0183c04000e50001c14a0400d98100381d81e00321088050f041c0d94038a040440c20100b000c01078140c00c0e1706003040d100c2410040a0545c420140010f4a401c913070700c0054110301414002c1904007400d00b0031540c500768400c4811407520000c907805000101c048030207442452a200020310542070404840140c1c202d25500c891524800c00c2403020307250855a0002d0441e04100d01d14141c181c41085410041400b0b610b8140c3c403402d240010080c21 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 167529793 1250 167528543 167528549
    0x9060615040b0f0306041803020a03080a0b0f09040f02060d1509060315090302030c16051e03030a0809010b0907080f09071a0904020f040635070f030608030c070e01 72
    0xc600030030040040701d0140080c0c540c0340300182401039880d121000024090202040801040c40b0204810000c044d0000b6840301110320945806055541d2661100201c94481100030f4100500e822800f031140343c103011140c0e0181c400c07034218001c9100e64000c507000c1d4000404581420740d44044d42c0b001d10400c0000500103002d40d1200780003c07030035aa01d8134601400350700f115061586a8494100300350081c402d44510b01e01d00411142d0000480100f581048141d01c680c9004102c82101c41c030503040440000031420401600a6103080030b0b461084900420040450006543c1c40301d03421259a180100310307010b25402d40d516216420035601d960403c542c00f45c00e4a841d64001c1908001d0f01e0b0040941c0000c0e4040341211548600c15500801c0c06440fa030140545c3c1c0100010300468080d40101078046081c03070140540c2d10407061444001080c02c7e0079040b240c041e891000001ea081803140e61902c1586804d894085403880d80d0f0044d40349581c108011000b007640164006202e100c0c01000c5203801 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 167531043 1250 167529793 167529829
    0xf0312020111030c0a030902030c06030a0f061203020a0807080f0a0e010f1706061c05010e0910060e040f1b0e0601020f0714040903200d1202130b130e090606 69
    0x6541004d051a020340d1040180c01828540c17541c069400b5541c0c1806240460f82c8041e0000750350b80380c1130101030001c180061550030f01d1490300d000032550f0880d1641c054402070741a00203100d03090b05604e8041868014103012903280501f008010ba0908400e40034101102c02ea86807005088090320000d031004030046c15007410003800d0003224221031f62070b480d03054100c078043e0390032a511015441c0c0014602c00409045142c02c2c14540000f609a02859509110fa11408140c81201c48215481c500791a400e104808014410101040c01301d0b040940300081e651095031804111810100d0584444011b41d01c000d03000b022a500300030403960103100d460000741d00b98026001c15410212809c90070030300c0589850080b42d6690810742018002c985000541580050040807041c0b80940299581c6049000ba000170b11903e04403050307001035000745c82500045031200d076221410240900d81d036801a110300b6807140a1043e001a420012100756070241c441d8801404403442c000003480a118003103810850 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 167532293 1250 167531043 167531047
    0x4050709200d0c030c08100b0313020603010e07020607020708121b0109050601090b0414011401110f0f011a100c05190c090501050303030108060a02130f090e061815100f0312020111 79
    0x87c10050b00c0388081c1941c814055a640340c0e2a00c880400c09024400f030001d402440000006c03418044503200307644114019800c071191651041c0080b078903017446100da4185603001020742030184284c40c01405402c41a00c1c400c03c003420050b240682524040001902c042d04048010300028140380100200c03200151420b014030f5a801a24031420181403182000c20101503c40d44040da10401000900d00c985800302d40780d008403001500d4485400e407081d15002d46c038000c644422050840100054800300528245900040c1c1c081038070079a501d14000c95141c000c020750581210440346810444500403071840d000d80e8240387c190800c41d40180c00c02486a841030004002d0550001901c40d8080c800d1000903841d0890322070038400c204800c0d0000d01419829860105282d000340d40310300b144001c42002c40e403d43d20303100c03001100c241c00401c8101c4c044c0c1142d90303220040e1074821a900d800040c80b40d000081a5640c19121618203056002210f25841c02c00750a04c029609024040e640b000381400b0078 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 167533543 1250 167532293 167532301
    0x3060e15072f070e0a0f1b08092e0e160501091706040312060503070b030421120e0c040e15010801060f050d1415100e04050709200d0c030c08 62
    0x55503a9a031031241c0c00f20100310a0018512000b10342054001441b030381b409220a100070030030544c1981c014065400040c1504000542c00300c8002180e038031034a00d00542194a10400141e042c0748225448014001c0d616030801c20f901250400c84400b006c850701c0c503080100d50804000600400d90390340000c1e40440d6000c680313038502c5004244203400c03e504d4240f60100e00e000124402c0039011940c000350380b5004030f042c0050700440c030000451180c4e02c00ca90548038102c2c2c194603058000e981d1211400082d03d4040159010030142d805103007511001d10450b120f401900700000c0c1030710100484401c0c01d0f0400c0c0e07440b8006014135840c45002d0600d02000748040760806840002d240418801c851041c800301c007000301808060480b0202070301d440740035104e00d0450a505140d0b100c0d01550072501d600c05920340001c99004000c1038070301540d400f4cc00303400d640f89801d21030300151592800510500311480c49908000c02d8440c01022011000440420542c0d101a0013408480c000d0311504d05100d0820200 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 167534793 1250 167533543 167533637
    0x614040e0601062303040303050f06030a0302060f0606040e0c0c0708120a03021c050f181516030e06070c030315060e012a080403020312120103060e1507 67
    0x9a040d210f10f40780403400c15030001585008440300c9111101d0341003001041c001850341c15044148128107110721000c040d00e40303100b8190303514008100540113800500110308111800c0d00b1054001c0d00c014440c5d0f04040d150136004200480c1603074640b56500e00096a06002d6800344092002000c0320405442300140342c00140d0102e20031a100d44080503030005441a11101c2c4620800980c4036072207007080b00d4039060040d407800141c20303110f0b0940c0b00880d960512180c880050520f028016030050302002c0c1e11050443d5214221a002c07290505031102507802c480f120802030317240b080c2001d80d05c403054040c9504001d0111200300e4006024001024002d12040303401c0f41a454114100703180c400ca806450030441030144080000280800140c0070000050001040c050002d4070300840a640180c1c1c0c80c4140350b00d0a03c0349116019480103040c0c010404604281d01c0402e05826520940b40b001140c02ea4613408000c0403250703400821400304401d8911502c1030840a8050110301908031905007141c20 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 167536043 1250 167534793 167534803
    0xc0d020705030a1203090803011401141306030213080d120b010801050603040b190203010b040302090c0a08061203040b0a030608060f0f01230612011a04050a09020f07150614040e 78
    0x10141c030300301a420b0813015841c440c0e031100a00d660015000394a039611112550000f501006c043c07800100c01c00d85079141c0040410403207080c02c00302c54550004074605413068001e500604841242194603c50000b458441448114180a03980c1da5000300c010301d46c200d11044404188105040260020050046031a138500706c070340007a00002e4030b8607183e40311003158080030403221030144114008000000c580d442040540700350313803003101d043d441682c4030091441c2c280150702c800c000103104000440c042d4103200404c00c1c82070180b5802e0300c0c5041d44641301103016074042c080d5200080c0e5030300010044900d041c820b142d00003482000314015030a00c0c1e40b401e050040d041c09000000410429644c0c0c1d50707503c1c00b0300a00c00c6400540f400740c4035480c500e800b44a01d030091203a4914026050724a090684144003110141d0700000e12140b034031410008002e00030741285420740c03503501040110301e000c00e58400d00180b15020451380403441c01e0504000a0000c60042c846501880c01c0c0860305101c54008030b4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 167537293 1250 167536043 167536063
    0x10222080709091b0305070602100b0a12021503010e010e06030a03020604020405101d0108070806010b07030e0409020d14010b062106060415030c03110c15070905060d020c0d02070503 80
    0x50206281e602400e008a444414032600948254501350010400001144a0007111200e0f001c2e1011001000104030035513503c140441da128404050910032464480080448a80045d1540e207801c1c4024420541c140d10a804c030304500c0004d0720041000611218005900040940207002001003540d0060764588000e40b001f485a901d90300051b01c030b5544401014014990035040f240595968400302d4030070380080c040d9000e5401000710108081c000000c02e0b50482e5841700b040c07481c0100944046485034111140c840e88030f83c580e20094003680d20303110581c8189002c8c0300400300d003500d140d44480c211624003401c2d1380916018172071988001d90381c5810345800038407d03840c182c0a03501e80c00016101c0c400c5070803500c14400841c81c5074a0740c5625030300c80204e90710f4030307181040140d0b0003040700e0180c0d016004515649900c2680035656910520210b0341c0c129100d03080c6041c0060310ba000160301c540141007411105030340814102401402000b011200c0320302c40c000740002608120101e034a5a110310 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 167538543 1250 167537293 167537309
    0x3020702180a0e0a0807020a080d0813051504051506011404090522030c060608070308180111010c030b01090512070515070b0a0b03060a060f05010c030216080102220807 74
    0x1070010700701d0040b0307401003a06400d4800645442058911346400c19030000c84059001d184440d07808200280000f445d02c40c0301c412900c5a064685d51710700c1100302114200801c4446018010945401c82000b41e2418015807042020700000d4541c19403402a0340e0005180f05c0c1001000608017021650110484091380d2040e040480c03559501c01140014100400d900c45000305040c015a062550103094480c0b004d2080405005181d51008d01c942c3e1440361380000707003a07a4070030440200390031001038030100c003ca01810902054410b520200782104c901040100209441e1001d00d485503a0002c030f507401501d4106d4141744120301c6010395654400b82d0f03004150040d8080f0b004110b001b80588240d89034103900503003611551400700f441340c01038041031204a003e44a58808912120080c1c0148420b0714061419000f60600e040d004544108130364500b602540500b6150102c009420101540540075050001d0b0351001c60072030b06500f46100d840c0b550581d003040002404144c00210350342040303810340 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 167539793 1250 167538543 167538589
    0x305010f0b070501060503030a080405060c03060603150d0c230109031a0408070c08100b2e050702060409021305010912110109180903080a15030f080421020f0103020702 74
    0x780c0f9101d401441e0503003040d54035100c04140c140f611035210840e0362089214105035200754440403001a6280000c0d02c03110740c00881400000c40d80c848501c050b03444260004c0c400404220305850b01d040703526203a00599101c8800c284800c000a06840160210740b50a117040007583d407440d2190a0210300840d9614045001d51001c00c1c2405a85070517501065041101040d00c0c1d40c0d1500245c1c0d03500854040341d003d450400c2e102d881e003440c2c5400c0501910000d1580c2c541e040ea0722818007400001c80e1042142801018860800580c9a0f8405000942034007100140c1e03403501512140716a022603800386041011500c07050042800040443d8000c0f07500014580c0a0100c0b88016646502c154010051048588801100c25800b50304000c60090003519400d815031148000700d0b041d40c00c0344580007101e0310003040070070000d800c0b00000c410181c0204495401c254591861b00b448118845c008010356601034922025407902c01000307149401d0900b011458401d5541c041200c1c40882003200361103c7c03030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 167541043 1250 167539793 167539807
    0x320040521030d02090405130b0a0c0504150c060e120a08060a210c0906050a060806040207060203010303090602060604090b01050f01030b03010204060201020409150e0f10050a060509100305010f0b 86
    0x4007800d00c0114480d000b503a403154400c80a0400a42040040074420340c01c001c04500d09500050760100c51582180c151a5039580f03c014110140c60a41003260801c10b08200002e09100141002141c441081e502c00c594140503060880580d0156480503027550002d8408480e4004104d080714164821814204800c1e62003100041c040c180e44d45c0144800100911a41110031903a081c180e1032030704c1400306101c29074850070520100c400902031150071500d009014007201e40145d84060340480f0090000d0710307140460b514242641c0080c0c1c41100030520680f000d010043c2c0500099030720071802c0da810482e8900380c1d1110841c0740c034103104030740c056190090410110b034400e401c105d032081006030082d90b07590342d10700b0024000d40c0544940844685009640d052003090304c803804c000c0314034a0801c046251155142c03124202c030b000d400c2d45840e654078040010341d034a0399003682c801440b4540351641c0300c0010100340720200881101c04002c1524120052004211002142082e158210300c000c1c2c462075 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 167542293 1250 167541043 167541079
    0x1e060b250501060b0f0a0219110d05010216050f0d051908130c060806010f0c05030301031b120c030210021912021005010801021315080a09060914060703200405 70
    0x81a50041c1902001c0017417a48a40c0340150001d11a038107040d403c07541c010100300c6194801400c060001030520300c950329611032600d07000700d003240998040c000041c81c06120000c03e0510251184d0b04841c90f80005940d152607103000d000d081060352144c28041e00d4100384103800080300c903201403400184450306012581c01c1400e142c5c6082400e5001c02e11966164607100b0207881007404949442c0061038000c802641103104604101209a115000354110703401c554031000c10125400f402081c1d510700c1d0900007880c15007420f04440c200e002c1c02c5108407641c10750040c80711403084403c1003019580b01d40070b108100d001d2180c801c0706050700101c040280388000030b0120300b0301d0300b03007800407010303605100010030046019401400564500e9002281e00b959584108070800b10f68003140c0040758012002642944540e046008094425000001c204241c2d998181c02d2403120030603070956510200c108460381e9094461101d03202030f0304000b036081880d82100650148502e000e16401080d00c130701d072207040103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 167543543 1250 167542293 167542301
    0x12020307050d05040b0a05011202010206010b0306150d020306010e04020702130c12320c03010e0c0909040308060f06090607020f0307121a15090103030f121e060b250501 74
    0x142d0360407424803042c209802c0c603208901058030301300c0c0ca035403400c800003132007040307412440d2941981078015003807a030320700540002160802800e4980043c1c05400c0c000300d00100c600106201d14041c10300584900b045400104002c02c00c406560241e0701c10003100001d0303a5040252682d41119520110713814204d00011107020403040032600c0e40c6420640418910b0354500e0039020100d4042c0d03010100800382116824003603005986203468141c0c204011300c2000307088444540d01c9074240c50001d00c3c1031034440c00b01e40302207070441d029030006941100b40295840c1c501e00c0744e40b00310812110981850b001500003900703441402c80c028032404501c41d180b4850b0700c2c01e1081c003006241c02100244101118140b020460004201e20000c1c3d084580c0003030307100c20b07045000002c641c00141440c802030b8256070701a641c59007019070b01002e000500042d0304503002d40f4003800e0070312028144029011080ea500410544042d07411501c0b0710082032100407030071050200e0f00240c100d0440301c0024403a042e400c01c54010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 167544793 1250 167543543 167543557
    0xa15090204110c070905090a0b0103020108100f090b03011b0207060302130503011802280308070f06060b0d060503071a0306150a030b010e0906010c080c010e0a1506151202030705 78
    0x107040200d803000c40d4000c04138144084131201c25003842290b0760620300c6c3c0d0310f0780880f21005042992900040c009544568105175000a4508500d0540c0e41c880e00035503040101503002c1480300791166500031030340c2400c1c01107003c460503104c0390f2810662410b002a444812134000c113420181d02013215440047c00d561a1001058003074001c10480c1414040c80d410080c90901c00d0340100724200d4006e1403d0380b44400c0800000006d03c0b06600c0c5030450391640b155a211000030b07038014040003030080200e0218480d020040030101d240d96540c04800b181c00054482c50f9010030b100e900704c02c40c00c0010b0600c09440e00180c080804101c0d54030391b81c0ca80051482440446064505040401c014820302e0709684001301108003622a500001999010840003540032039905000030f0000034040c0c0042c04840203000c80180c1e840010a002c0794000c040340c613140b008903040c1e070b681d40c0d100346504076240d540c4540e0018040000222107030500d468005072980416154045150b80d0000c00105020f12482c02d0700c00c5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 167546043 1250 167544793 167544821
    0x171309140702060c03151c02060309010618020c030913090507080102130504020f0a080c210f07050a0804030f051303060506030607030218010302030603120c070608090a15090204 78
    0xd40c0150800c0390240304000c848400141c46a040420040311903407082e248181c074641d50007040da010034400d001c4440d01d840600280510302490110042c0d0741c03403000d035105240200000805e00c1ca04541a41115844580300c12260b03c100074020398800302104a030210042901c1c41031b41c0948040c1070b1001407001d464003a129014810012034895410b4008090100c100c404092040f030b1a081000220310403136200080600d42000040d50ba503000d586040c1c1d0000c2e030b441d06d00741800d202940003407400425102042c090300900c0b0801c41008117440d102d603041103451808a00b00004401d0140c06003070051f101406010171010280c020601c1602207544010b181a00010460350324689407010f4241912641d00c40d0149030009103203140f0174030030303a00031058480d08540300d004400c0054000751701c003501c250340600500c0e9901451084600050510842e4100203001d01494600c000305540230240a0201c184c02c0b4103100c0001c1810320440d05245002c0c114005040c42c0507200103001407586a1603082 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 167547293 1250 167546043 167546051
    0x25050706050d05100f140f06190305090f0d051605070b0307030f09030801050f1804050c120d05030c0d200d0c020c0915060c0115090c0507171309 64
    0x200c003a0301c10040c0241021408040c41241c071400c215440c071403802e00503c10303500242d400c100300b10095180001040b40c0c014009061010324040880c800e40d1291240211503450800c0c03a0a0285d4503208507980440880d01411141201c11255501c0705408040c0008100c40424240174102c3d1040c040c601d06580300048488540e81c2c1d14482c50302b600101c3d91035011a2825525145281460044050041d490fa0b141111603003030900700b0501c40383c3c01c1b50075504406580d62282c984200c40b9010b41c041ca000d10002c0040c00c03000d1082001400c0c007000605901e030018a140c0c01110f400805403030b040445c2003072464848494180100042001c0080310080c3e0f0000000c4501c40f901040081400c0b58102000344044d8603008800e036903c540c1b4103c0e407504210560002040c003601c40980e03442c0b00400401803450200b11751011400d6507001c004440b11500140f00400052403180724a0a841449050403810320200b0340b0761021b5000d010300800c980b54800a03007054040c0034903010001030314200000304 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 167548543 1250 167547293 167547299
    0x8030a230703030b09060108270f0307050a17130b0a0c050a030c03020f03040608060f0f03060403030b04140708070c21050c0601050f031c0504030803010e090606010e06250507 77
    0x14060004442d18a000305d100c1320114009510480d1401c0c4241003143c5044000707000c0400c489044150254190f007140601850001203a6080c0f0017050214005c0b40108000d440c00d051448102d82000c039800b51a500800c1803d00c222101031428003140c485020107502c6140130340050356180e200c94002032017401000b0303d080400d6008170001003600d000ea421110858941c4061039034910403402980c2c0402e0003040011418030f00490311a001a80c0900985101022480441d14021050310100d000ca40c444804041c5400c241c403500c88000d070403c0010b40d05080049000c1c200c2d41c4040e19800412580c4c9080c0000d222074801d0411440161500480b0314040d0804010100d401180042c40d4038012180000382c1e0b80303030518068000c0c000c000d010705402c0781d002c001589401407030440b045c10700c0000c1c800003001c03d070488059402806041c0d2200c4042c60450700c507a040c144010309a0741804018040c0c862a601e4003c1642c0091140004104129414140c0071505020180c401811403003180008 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 167549793 1250 167548543 167548547
    0x31719020f1b0606011b020d05010513030e010206010e0601031802100e0a0e0402060f0304031407030e030c01090b040b070f021306080d02060601021f020d090c0602150108030a230703 80
    0x602840310001c0c9091818001c0b508615203584040d0b401c1c500041031729035404203000c0b41c2d100300f03c034251000b000c4400700049a035540b800e54004554404403901d102c43d9807000c7c940c026501101414091000d0a01d56043c0490792640311400381c0120304140d034480101c0500c0d003441400980182e00100460706941c84200001d1200242c84461402014501c030b0000300400000c003214061b9600401c04c500300391405d0101406078100800c15801c114211503403000b1b4500c694000c11115020303980e51343e03440b0040700c00e041c94400d100c0485410040c1124007000444074460036202940c41e03a28503266184040d00382048414600c04000c2c0d4814079070070380444240c001c1c0c1d2152040342d0409080d00c015032002c0e401070b40c82d0801110341e1405a04460039004207541060700a4850783e000701001410026403c03003240494031011003c44031140c07807038401e002c416010066000c04c020150f080344220342c14034050341d883e401100066400e12422046107140051ba0101c0c0305142c211044505488504900300 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 167551043 1250 167549793 167549797
    0x6010c0b0c0901180e040803042a05090f060901090b010509180a050c03090c0603040201090305030d0f0e07080a1b030209090102180409080306101e05130909031719020f 74
    0x74090106207269800d500004c401a6404101c03044e60f02007502595594031031040320f41c0001e1089965140e4000481c64002500c0c03168500070415038601d00e0038608141c1400790404014151a0303038080c403481041410780e41c5416441c1524140300b80400c0200651005840b0350141c54440703684030265460090020740020440352144000c035005110507115404505000c1c4800c0e0f84011482d0800c29005085040c21002540c115106140601c58036a81c0c0d1149819a04020255000d564030758410400440c050700885d80000307564800350200c207142410131641c540700020000d04403030f02504040c41d0000c9510303020005580141c81c548030744c03401d0110103000350f0000d51030692041d10009800254205441040003c0707612100c0149192607000801003103c002d001040104030304401c02407810141c015408510030401c2d1201522200301201c96284060b0580040800c1c1e441c040f000c80c0440d82c044413094682035500e07084520b07515005601004007034a40c409520690000801001051800c00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 167552293 1250 167551043 167551057
    0x10b30030d021c1401060c030815040e0d0201141314120403031814010c0b090703060f02071e0803041205160809040c0e060904240303030608060109150b0306010c0b0c 73
    0x20f400c0103044040b000e05191001c003800f810000401c10012100000d02400009030000c0b22449040401c0440c107000609485200c00070030540d421203820350b03502a07024000c100c6255880c0740314205d1413400040001c40781d0a81c203005050384914000d4022542c0c000d10a81440c540c3e40103110395615100d05000c2d02c6c2203c184070b900c120172141030000a91014580d05012240d4050350ba910742c0320300c103841d80d07101c0c0c82d0040c0820f44280503022000001440500c100180d0124040e000351b00c0c0d84850428461280303000c070140d14000d4070030482e240010481801c40b0f5019070703c83c420039061030400030202c440307000385087c0d070a40680700e010300420710417601c001d0490500c00b1101402811481c0c64101d80c0e080d400142590040020700408080d0710b841d4101c007040b140c01c43e1801c18004480e00a6a0701e00d00280e100b9000702c1d580d580244000304d400d0000b503014090022050041c55045021401c06010901c1401050b400220106000341c0c4524040803109070000d1844115003400d01c58400a41d126171 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 167553543 1250 167552293 167552347
    0xd0509030d020106120f03020c0406091d01020309250e09030417160302100c080d05011415180607120f09050307061e0c0507080609010b30030d02 64
    0x400e001e04420310501032502903860f000242560000e090b42d5240c036510b08243d00300c0640c011700035400c0d0345880d6885480010070342524045400140c01110043d003801604913040242d00400401052540000754441524a50440030b40c2600d0f50101e48050120707a50030840000c01c082c0b06015240300004050801d1303e03480b604030a541031262084a44e1140e20003070310004014291001c00252410520b200100c0100d41483d041042c00341d40d5800300740c1d0101100480181e66207005200036198010204c48030a000c1d102480c001001c0110030285000d12800c813609400b820741841110380311101580e005c8d96102d9400110788840141c080c0500c448003240070300103000c4840c0040c0d20301c0c00286240460780c031525450303007503201c41511114007000b664100060000003128400080d0301000980d0051040c3d0015240354104034042e030703080d80d40b101703015131242500d0084030114000345d13044010140440e81d09105030180a100b07050850142c4652243c040f40b000c602c0c1314107003140c290309440301080c40e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 167554793 1250 167553543 167553553
    0x702120c1306060e28030c080c0f130c05040e07020f060c16032a1b06090e0c0a020a150e060108010c1b030c081614070302030c0d140d050903 62
    0x89070100c0e00300c034107a01c81c01c400200501c1e5000f1507400c10340220307400041141e804101005003c500300c641c1044650045584a01302c00b030401c5403080500c4602981c00048400001111010001444000d101415000d1540d510003d4414032402642110010304a09030760580b10302d04132001a485041c03a1042c10254041c40d400641b0f00c41e0071800300c4400303442d284e07041480c4204545084035008580c18114210513440b13044503054024808180003e684030b204c1e41c00003100c071034043c00076640c110f45c03250043c00340601c800c1c07084007025400b4540c4450003180d50781c0c035030a011804a00d006180240038085902c0c3c0c2d0044564201e054011902200140302200d0076a41d179007401908980403003890000142d6040d410380200e07140c401d2034801c840d000e46031802c40c8182c00e49410025a00200f0080d8001c00c1c0c1644100410104000c00140004a4800303080c04034a1900403e0320340c120f54038001e110345904241d0008000e0601d440c0d99500340f00000b21649030340103d00140803a803108800c41d10034403032 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 167556043 1250 167554793 167554819
    0x316031103060c0d020714060408070311030405060702040f0b1206100b09100f2c0a15080c0a030204180203060411070302070302091008060709090b2b05030702120c 72
    0x400030b4028041d10365000c5041c50059003c41400094000020894801101064501c0984010480c450065004000903662450289000b5207141207070030300c40086400c00d000402660b9a070718180c81d04c142e010383c0d0200e045001034140340000d20350f8441142e40101103141100c042480062800e1040172540c515817101a195070501815009510503a070340006030414244030b030b03845850140a00f51260030998000c040c48181ca00850249510b9204000201501030b25035141224800700200818038450085d21100c000041040b00d00910b0800700c524001540b40ea007034070a6040390000c00c41c41145031000c200d641c42d03000195005803883d9100e54140440b15206442c1c410884000580c10340052200900c0c55081c446103040040002000b030a9080780000c5802040c810030b8400d00680e03440c00499814103a44004441c50b095080e8061140080e1809050030700100861400c0e0482a89c41910103c0d440c0c010326512030040001c1d088861289181340300f43c0c00241d0b045080504039200c1c02d0b2924 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 167557293 1250 167556043 167556049
    0x40510120f0c2c040c03060b1b12070b043201060302040b04060506030a090206091c050f01020322050a0203330606090105130302040c0c17030906071103040503160311 73
    0x2151004020300f076229600c00d8582407410764065519640a8240801d4080d610b58920225420052401401c00008103c40c0c8601c9818000500e80d0001d984200703080a046031a107030582c0030000d100800d070415045444901072441c900c05403030b60044081c003a0700100402c0a89004c2c143d148401c178040c904240b10300c10b9524190049078180d44019160a045542e21084071024007800b0300182e8000308100108005031301d801d01c210803c0d4480f440d21115102c8203140032850f000800d40610710992050044c800e0349940c583c0850102c44040000505400c0103041ca10f042c81f8401c100291305100b00c1140b2841d030b0384900301d000704603400c0c0402c81d07540101e00c1c00c00103a00e01007180c0c4140d100e2010060180650b0080c005010588040440c0d00702c196140ea010400301d403400c0c505900854016041401080300d50307144c2880301004140e6003421414200201daa0b00c0c00040c040d4400e0150280742003401c080f041064400500004040700d0700e54000160240e44140365000135a0486203044d00345d000c5003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 167558543 1250 167557293 167557337
    0x6040903050f070609020604031112010c020c01030e12030f011e1802070602090307030605160306150f0c12090f080102031e060f0402030412020f0a08040510120f0c 72
    0xd4064072414640b10010310254210b0380645403c0f40d00c0c940e12080b0f6405031712140040c0011b98840c42c80e0640e1002c41100304840c51851140131811a8108200d46c08219804030740031039481000e00303010950f805140354140c100306d00d201c041c0c94800d401108004014100144417030489001d00100d0300225540740c4000303900040d070700075401500d0050a280100d60b807541d000304081070003510018146403944001a08004a6038026100d40b034071842441021346102c0210703800d440b03440c1010001e4138902007620700400b104089150521000c0f8116442403401040000311351503100360070ce2107450310750401801c0c1c811700d0700a08251142401000c01d00000501c205e90241109140041a1240720844480300040c01045981c02a03020400301e4400e455a0003d540918802c2d82280111440418024034113100d0480002c6d6690050303031180017061118040720191031080c0c4802c00c0705000d400c0f0030349002d150f4a42880c03085103420381d9000c01441c150b2080c10300c42d0b9140e540602405c02485201801 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 167559793 1250 167558543 167558561
    0x60503010e040b0604090f063c09030201020c060123010f051b07050414180601030c17031905030612010537060b030108060c07030503070c1406010b0d050604 69
    0x50000007001c10041203002011075441032000f007001c600040350750745e04940d10001c00e0b130444600e500d0307540210046a000f40807845600c1e1824003044500340202c0c032510840140c140c061007050751800d241003450f1003901224030752000341d0304540d600d507914040c1c5338290044808a0381c0c84010964a009190302c64a80b0340e184114942d5160709150580c0c0150348510700c2084800b40380c0c4030b828000135080d1a280184000503901100c040380a00c0d108a0407080c00c0d01c10801d0819a070886401400042c080580c84410385042c0758100d005643c01c4042c1a18501c152104510f96140c0e81c3c44e04c94629a109004500c230384801d540c20314841143d5040f542c2600c0c41580c0134140c031406056001c4030041c16080440c408404180c1842c1019103400144040740c1c3d2607006100e00d08000070060204107820400240c011019401c1c072803800b402c1c0e4800038128080a030900b01000488020f440a1004549009116680351010307607503507580d1083c68102d1907006c00200e141d45800d2500180071440c7c284108044 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 167561043 1250 167559793 167559809
    0x60603021305040b010915020c130905060f0705090405040b0402040c020105090d050d09140a021503010305070306020f19110f0c09010e0c250605010e060d060c02030d0f0c030606050301 81
    0x14500b400c0403c0041c041c64901141007010b0784500050480e03d1508602d600c0700141c02030000f40c0c08540620001000c18854000d0700c50400c005100001c0c8005886941302920b10b04c000e409450b9150102c4840c40b0398003a480d0f005082c8800d002c00c0c840460b4009006500c00c03101002440300c4144c06034266802200d0308903040e0803000c0d0419206c2e000b2001802403901d41c40340003441034041d558562002000454844107640f00441800441c240b003030142514140320030b010340c01e540c9540d58680c4d88a0a40c00000c02c2c00e40c010038444100488402900c010f400004d40003149403031243d030f00803d40304406030160441d11602c11994001c080110390501c000c0409020f03000d0350fa08100f000e05d0300c2c100150010300d4116040000d0b8041004544251828149140000011001d1802d01304243c61041e0000c0e2110407908040c400156101030000d8640782d4000000300d0949003000c8141c2c01e40c0a028810510341e818452544505e030215441a10074500589080110580301d0700e0440e8a80070901030740d00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 167562293 1250 167561043 167561077
    0xa0b0f0a05101a12163207020409020d030e090a0b0a0302060c210307090e06060901031e02040909020a0909080d05041b0b121501020a0b09010b090f07020106060302 72
    0x30450500640030403401c15900c40b80f515102d5050f03403009000c0411694120501e0782015051850fa0340003002210340d1020201940e610349084509080002c0c4c2c0703542003400001c00165071011502c440e00300134071176900102400915083c504002d040c2c01000c6085038400c1182000040480c8100d10550840d82d0015202000c224115401d01180754805010000b0b50b20a03506800b00000e400c2c00118600352074040e6254480c1800b42014118555079042290030500c01c40801c40745841d82019500707440d1091030040b070f5840c11040594000204545280000f600019001c0b40c186440c1e0803e000540c42070b210921034680e1036485a049510b624402010000300b001064651a01500f24641040c044c1004420303e000d10622603250352070700d61200591ba1001f141c071100020b0343c086405e602290911000c01041c20280c0001d448100c0000024070550519000c80e0103114254040d47e01c602d0040e0541c0311074106500c42050200003200c032000150300303282001ca07226229000b990009509511042 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 167563543 1250 167562293 167562299
    0xf010c11030403022107080d020c030d27080f010e0f0c0d1419140606010806011b080c030703030204231c05011b0e01020c091003060506120a0b0f0a0510 67
    0x2401051041403117240404101100c20300c0010b0203004001c104a0000340542a512074019060000c0030040714466004210020005500038907a40340f001d0350201c0b03d840125100501c0d5000c12881e41004140c8d200761591103641110560100025a41a8044a10180301d01a00641e262803c12429400041107075a20300026241182c0080c160700c06011340d81c64010b8840b00c2581412a030800303036804800035500002c0c4250038000c050b0403002c01e1800c00264038190001811060148041e9840198518421024042c8802c2a00c490100b008162a81c501403818006d0281d00940030703010300c030360b1290307504d521480401807100340030f001c0545030302002c81d60107036082078084074030006079803a54030b48000b50070441100d58141c0740c2c020103441d80e010020110000918001182d4100c1d0f020740c1c90760f014807610f1310100211100312580881c010809543d0072000c107a5040040c003c0d441944914554a401c0080b010a507501c18400418010540d5542c1c3e4814010303214207440b2220311440c50f003024 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 167564793 1250 167563543 167563549
    0x603050c0105160b070203030f01091a1e0406080c0a0816050411070204020a0801080c18041203060308070606090b0d0f030e0102012d0f0509030a0e0a03020907020f010c1103040302 79
    0x141c40a00c201110a0300340c14000c4e02d07100000441101c02500680000040241100c520524a07016000303450040050b4a440300c04030241c40f46000c50107208011000304601e5021001c0c40c842d50040d0302410070706c1025641c021071030740c442c012418a403095420880114240d840020f04102d04208800d61a03000d6241ca0305201c0100403468a040035480c08200c041c02584880c00100707051031542e555202c0c17030361410000b1420400407031607080c8608800003400b151000e42405041d0083d0f0401e24507515420403400c00e400500455000a02050b40070030510180300c00355200c03c04030f604080d001c1c09054013010030449454480b00005110312652406003011034854060701c407103160180000a500400607907117003d25007605481218032a00d1042c42241801d50f40120714004000070000d00c000d00309003607a29200e000383c44051003040b020300344030240740c0e0781d0703a48080080d0707005001c00050f400d0404009440381c244c0d400100c030640c00c02008000a40c130901c541c040f000c86203000395052600b141c0c20 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 167566043 1250 167564793 167564797
    0x309011706010c060c0e0a06080c18060706051608060108010e0f04060f021902010f110417031207080121050709110408150f0a02030609060607060207150510090603050c0105 76
    0xb410011450141000181035220746036070040281c40742e015120f915010081d00d0301e501d030461420011400240700030071041500b035450207802e10008441040100012500c0c40c080c0100c00b614003070a20043c01a403c5495504a101880039038801450790348400c01507502e62000e00c21014211030000020f0248040703460031035007241c0f040c00b001c25080d040a43c03003800d0340c2250310851090500310840009031502481011106542c00c2001d008601ca1400f0701c016030b00a5204159282d440c19101c11824107082c07044624000701d04803006205d0400d028000d041660034043ca00d140100b40b500c2400560502007403489042e403100043c181981412001c5018090354071000301427650501c070109440c1e90504c0700c240005482140072205150450003508050000b0b81901c10b602d2040040c480103403212450a80c0c0042e045c1c9003140d44980601d0468000d100c0d803400034181064016400c0040b0031503070040d50280c241d4002500b40c1c45e48800d480c03400c41ea00343c40300605652001036004503550007080 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 167567293 1250 167566043 167566051
    0xf120c0901050d0507110d08010f0e0906010506070507030609030c060507031b05090d0b04050a0c05190501180e0f040c080c0307030b0c090a03050105060a1d0708150d060603050f03090117 82
    0x680030140400c5496211f180180145084002c5204070006108100c4a0054000101200a584240d608080032082d44640b818000c09025800c00500201408400c0000d00d000b1980728000300000c0c2500d080003800030440000031105141030401044516103e8007804001d0800c0c4140e1405400800d2801e1341c55038410240250004451140b2002140307601c241e151240e40180c01a002c1c1019600d02010410025003081d8800c0e40044011540507900401000944000782032020003841101b40301004e0034890b9103e01340140562080085002c60940380a016a2080d0f132718461b003d840781308040e100d400035416150554440082000450041348034030b90445400c00d406403070000c1140c0400e2001c2c204d60410382d440d039101c0f0240b0405d07050070848a03004000d10815080721290380028046140c001070212010001e905022400c0307400610f0b060500e0316070080c407040a078401850150090101da11041c0c03005c0c040d441411011041c080100ea40030303e8140d503880a0b101c010982ca91034848060 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 167568543 1250 167567293 167567297
    0x1504030506060909010f0905030306120109170a021e0a02191406031504020a0519020d050a030510050301060807030201090f0b0304030c061107060506130e060a021b030f120c0901050d0507 82
    0xe030045d5110b52034424030503808c0c080c401556a9203417050900c441c102280480039066031400300c9490104c0d0302d0818084000802421081d5602c3c40348408a20f40b10080030f801c1084400b0103107906035524006003d02c3c01d20320a81d6400302104079241000114009445010f80d070000803a0f0000840c0751101c005c5034081c064800020040c8200004a0100c2e04150040f0000c6000040e00301c4074010441d8107103031041000d200401403828004002406401340500740e20625440d240403e441d0302d1a081e80c1c002810016000700545640d840250343d4801c110311050b40818284407010450401c0c081c00441541c84220329146140c4895400700c45840d40d48006803400c036a1224a03246c040840c2c1e0040010500800000c61181402070800010215801190381480c1c64682c445c5403d0a0106013254032a210170780040e1600b480022441e80e44148a803811518000041c0c0e0791b40b4000035030041d00c848480840c08030310310780d030340b04030700d500c62042c02035042c0030503070030310052034459071a0b000142d1200940c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 167569793 1250 167568543 167568551
    0x91e030f06310b0403091701050103021e1c031d010206040f171c050103030f0c020102060402120313030606061103120a1806021201060e0a0302090412090f08010209150403050606090901 81
    0xd07071103e01000700151821000103504480401c44003644281c9004040754071300080050303500d03660015452a461030080381010b140859880c007540d4841c5148124481030480c0c4505000c0d184c64020314144400014440701d820300c0303007102070b254400581c0e6403041d90710428190000020f602c4480e00c4019110751502a01410407804504412400d04000a003210807008650740d41180750103407442d202e0f80700c820300708400403400b0000342c1ea001500342d40290701a214408941501003009055218200042c2e0000a40800000400c0125401700040715002d030343c3c280c101141e00c42d40545921a40320315090841c41c1c000400e0f4a14040d078000103401c0c101c2c8410300407120312550f42600382d0b00f0600c0001740b01d08048004201081d08010300c1403840004075420042e541c00c42c1c1c001003c6400262024006107248849a038840380906003010240681102c040328103555500d03401e003c0d500c003800e028000c101c0d00c80c40d003403031a00000a580c00c0c0c0c2ea00c10003800403503640000340507003154010560000e40d929 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 167571043 1250 167569793 167569891
    0x70b0c010b1306030507090c05031513020a0804050c06071709010e04110903070519140f0d051c0825030f0203011e0b040305071505091e030f06 63
    0x4000c103241581400a0700864011328505201e828822541d0180103030905113101e05824a5002084982c001c403400d4121226110503c0482c40702c10100710710190480c0700042c0864259000707054544128440c41c1201c1e1154210b00601c05a40589030f00180780c0c44002518410340e002c3c00d070190002c2041072401e11f00c5040385a0000e800e9075003000940c150f0820015105219003000c0c042d0801404080e0b40701c484c51904401d0440a0b05490704c1400003519689202108d15503032800032080c0040300401c0d071084030b081400c00f29190510011280d040c00507007046504528086c4901c20321586110004103c001d003641580c44680e084040b41c501050b6172581fa8050710700c49440654080d0004040c3c4500300940088003511500d0300c0d0f0030040701c2d080188000c000040c00046c140050740c01440f031400b0a00f6605600791410b0003109402ca9000c014a400d042100c40300d40700b549a0010201c040310382d1203042040c5551942010756039604108070000303000c4017005604698020359420b0a40001360113039 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 167572293 1250 167571043 167571049
    0x60b3a06080c01030b060d02070302160e24030a0209061815030f03120c0a0c050a050c0411071109180304150f02060129070f11010305070908070b0c010b 67
    0x16120222140903590041400601010003512421480c2824200410f58512000400304e001d007600182500d900000c8110805109020024074101b00480c24100c1e035840f08600500c06070704451018035a0700345402d180c6082d1f0285c1b0303140100c08024000d030000200903003e000980e50700a28250704907040010b4442c1c196042400d80d482248141c00c001e68452000c0d04042c2800008801841c007a1320030701c480070311441d07403031450b90704000d02d00d1030a560f0702621301d03054a4078180024054883c0c040e2142941c14040b0110305040510400c9900f085594003980c20044d041c09150006007000f0035100001d119801c050700c03000c0d002040320440681c1c1104052403246564815007003850211100f480001c21a60444000010102c050001d003800d5030400107208000003100042011a5840022525440c00c0f4103084551154000100940105690400b00c8030001b440c400700d80003e18140005541038824005ca60640d988500a0034083c0e180940c0e203203843d0400c680d400039a5590f03041c8450299 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 167573543 1250 167572293 167572387
    0x80f190b120a050f0111040612050601030e1204180501030f020103090501110403030c1112030a08060112060e3102010809010204170f070f0f031217011202090109060b 73
    0x7503c00d00042541413030350030425094804400b41c0082c00f4000784000e01a003a0048248020201902d10000d007554690b0012006001c120159480c14041c45000c80e40c09011000188150ba5062110301016408844c0c1842256400d20010b400c46607402c1d00040198483c0d0030200b00030703002c2c1c00003040e120003942d2200d0300c0750b000b68422030225040f00106020400c4901e84220f48400854007845060f103100f940d0fa4691080711440b20401a9200006025038000c900503406800700c61802c01060f62245510500010181d419a55504130b04100c040c0c41544541c03400352480c071706044102010126801507581c0840940403682c555000d11000c50030b46a8500b0303181c0b401036100300510140d80780d05103079400c0c8202500a11096200844240700c81c2c40c240340c00404484d40003101d410020030141086a001e40da00481d218803150791400050682c0c2030018203400c4900807140c001459030798031882d41c1140c001d44035002034a04184002d20b4078001c60031165035141000c076100d8480300710003010ac0c1000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 167574793 1250 167573543 167573563
    0x1051813050a09061119140c033c0405010e130f06052b0f0206070c09020414031501061b120309060b0d0c0306050c040e0a020406080f190b12 62
    0x2903640d03e4140c0305100c402c0c02030032010010100611300e03158a01741c080401c010000700704414030001424030013130500000121007440c10450250394440a0110610b954180c0100390140c02c0a03141010030f411b0b050201c15541c5403142d501e059071409280400640e02502406502c59101150b881018000901800782c03150364031040800150305420141002030900340c40701c203c03204010090201030340c0b0011403401c00c00280c00000e41405180c0030320000f10240b04086006080554081c00000e00780c41c2740e00038106840c00810b40ca00e882c02c109003403580c0c0f100e80e0f0300c41d1840c48001c200100050ba02620080c00d0100341d001d074400c0421316a49814185010360006200000d54504404c0c06201c45c5204c2c007041240d04580c400700500f0300e07131a41d68000070180000b62400c1d82d1000402c400800d00f2040b00c000b4000400004550b2909044130700c001c0d0007610403c4089402e0500280c0c461040d02400c40c4a401d00c84e440314554410180c48030000d00c86400032540080e0b41c0055154540002c00c201d0b01c003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 167576043 1250 167574793 167574811
    0x207060204030b0f1b0711030f0106030c05010f12090c080d0f0816051209210d1a03030f07170d020310060302031b0304051603030903030311090105181305 68
    0x199a02d145440000715500070b200b2442c10703030000140080310040c40003182040428481c0aa01e8680c0c03420007035a1640c058192540c90701c1281039242c1d4400c419040001124051070030204169666001501c0b9070058581c94400074214224116040344141c1c4402005030040340050b900b44d885125083c0b0380440c00e611440421001180c100c0c3c01e5030706c054101d0b0700604003084403002c1e9801c44809481402030408081140444100080441c54108002510b04c1c10310754103981c000003072010301400c5034090084442410b0500e0580c190b2003c4c0c0388020304400e207024004518005030550111000e40110900700c07900794803100c03808a03180c0b60401400e900700c10a540113a480c1408842500b29058079400001407500500401602c0a02500751000101c003249205507a9652032a2a80c02c0c0340c0c0c40341028000c41c25402e00402850341c0000c410341540d00c40d071810000e0102c030034844045800b48618850000d00108030241024000449525900d03070042c0050041e849044900000c2d40c908640c042c0e0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 167577293 1250 167576043 167576047
    0x1512040318050a050f010c1b0f060201050606030103021011010212070e010201180201050d0207060603150c02191101051b01060b090319170c070b0a020a0b06010f080a0e0a050102070602 81
    0x162014070a41d0800814044403040641882e0202142c443d0300da5070382c6103050083d0140304009010042c2004100400ca0410800d4556140d04030600f50980c02c2c0210001980703882c0028445041100850741640d40042c948040042e21040489012903040041c0c1095502840b44d90400c41c0c030252101c3c005c0702540c03503c401440410000a08594040b000d0000215030b070f000410244c3d0700308088507003d188034100541da4029a0902c00003620041d88010700c07030540c04d80d01c60807e5000c1e62084405005030340c00c0c2c0300d09120314400300a010400f8803000d006000030103140c0c9043d6000e5002840071503030030b0441001c42c914602c0740c5400c44d580c40d07008460401c0002407854483ca014080c042c0d400035103180c0042e070aa299102c00d08801c40507040c20b64840310000e0382c0e07401244100081e0004003404003180755180b4000400a40716140c0c01421540039031105c010982660141007010110199696100440d985074801640649884001001d10740910685440071901c280010000700d80107c0c009a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 167578543 1250 167577293 167577317
    0x71e0506060f041406060a0905060315010306080d090b300a1d03030a230a020d1401050906010c140703030306032a03030309080f2a06060f15120403 65
    0x10802c01200c0e0034141c0300d14a8031424010f400142062281c0000040d52517544644c2000c8065a0b11607040d003007a0340c080000710402c1b5032803841e0706038110202001c2c1d030240310b800d64a0082e165103a000c043c0140100c2c040500078051105000082c3c1003401c0c1c5244c0041103e0a51814100c0580c2d0326041042c4403004001005a400d4540c0a120f000c1a01041c0c3e92401c505d0001000ba01d900002d04001c0c01d032500c1e0649405860102421112582400303007005016003414040d18000354030180c0c000f101e4074200101103210005010303030141200c1c0c0103003404c0b20035a200c00044605040c0303401c0803524990a003100d07001d44a420814240514440e45000402c0c0e81141403e1a401e07900028800100140002000704400303052134a104890345400c1c04103a80d180c0c0e00c5c000e216409070800194030b280000c50088002d012504c0303c501c034084440c0c3c0e5080700c80b01328422691214411103006810046900004526040189501c00f600810300300150510301a1520034160304019101600045d800e01141 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 167579793 1250 167578543 167578549
    0x50106050a030b060a02151e0c180f0109030201030504020d081c1808040b18040c0306090c02010902010806060702030a020409031806050301181a031005070e0402030f0c071e050606 79
    0x1440f030030720080354154103143c000c1500030343c1d0f80c1f0050103002d9084058004550741f004080885802e035218070041040711302c0c04064a245603005180c0b048003800380802c0703030021400c101c0c000c24001c0714103035160003465007150015800342c000a081240c102061180c00c501003044131019204030007602c0a040d81040400b0341201c250b5000c0d58281141d0311689060300c0000308104112412601d44120341c644407000e00000300d100441c20118227070400c0c18502c12008180d410707803140041d110444401c0115005d018403c82c01c95101940c001d0101c4c04007030101d0140d161008c003804c2c4081c4001c0c00c5078500322040e40450141c0d00e10806c00c40200e080c0f5451103400d4040c0006070320152045241160442d850401c0d049a810340132100c00d4101607442d81103181d00900001c0621405002504072804491104c510600a05040701c40f1030000340c0b41245080d051410b80201ca0040c1c000c109a00c2d05c3e51214642c030391940d0301c503981c205c4018140d080d8070821111a245001000390003103010f85468a485014 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 167581043 1250 167579793 167579801
    0xf180706080a0e011a01030504020a030515040c2103050d020f0403060b030d020a03020c010507111c0b010b09060d0c2a020103052206050403051e0301140d0206040905040c0306050106050a03 83
    0x703c3d100d6414000015410038420700c0d01084408246004621a01c5d80d0012031860b03291504050090b0150008050144402c901024080c1d44110741c0301c40072903912418200c0d0f0ba80100300d20f401d88020040103034042480345000d420404201e000c0149401058a1000c40075401035004890f00c5880380c404e24100d143c184010524000c290000d03048010180e98000d440c0c52448240701e060240100b510340510107111401158054040c00000b0710146450b054085206500e104031080c03c80e6800119800e004802522110316001e401c00742011402d500e0f000142c5030000c2c0c088200042c2452400c04c2045000181000310b5040c0c11624140049000050640c1d40003002c2c000c0404a800e05107804203204031089401640000001030b194035545070480d00c42c803c2d4018481215020f00d041c1440420503001076048400490007600c0f01d000c50402e02440d80e024080196020005000c100102a4540c110a40c07240c0715103030014115449955070803c41c0d40030f07003003a000140041a01e1148a0309031007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 167582293 1250 167581043 167581061
    0x60e100e0d0801030b0c0c03070204180501050601020c1c050c030a0f0605090604020a05040c171006170c0a0813150603020102190507060e040e0d030b130c080f180706080a 75
    0x14081d0b16035815074a90442c103aa000d03000681481e400a10050410b01c28020385d8140b5a000300144140d07100342402c5c0030750b42c90010041d03c07036520f85800701c6d05640c00010442e202e00c1014140c8901140d07a0040e80e00745a0803010281c0702800307808980e004969040c044081ea05100301c000701011500c1e401d140b0104d800003444184140c0c800014480035030740300c6500e68202d980c100c40101b141501d25104442035582c802c6540303200780203281030010400d0400e6203407065540c103aa82c0c1d016090400c1001202203029203001100d68410441c0e00c1d089071041c6070640e0b000c0d06c100301104000d10559600411551200c1041c00301315074030803081c400c66905114000c0412014540203c41c0a03040c0c070b0f4240c40c0c560911400c0305010801000e410941ca0341c2d0054403400501405684070080505000f601801003082c28610520724400b42054001c03481c8105000901241c0d900c109a984900e00880030280242c03440b0f0300f100f0201340c80c581d0400d00300041d0010b0609030750b6411187c24621840c0c01901e040701 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 167583543 1250 167582293 167582297
    0x10020c040c0c05240a0207050307200f010207050603150d0f120801060206060307060513050604120b070f08160908030705010c02120909060f1c050d080a0522060e100e0d 74
    0x8200d1070720401413400403d41000700b1520041c0c0e5012640741592842c411004014511921444031808040440e2a520018001583c6d4605c420103114012600d0780f4031401900d5100e071007031000c105103141000c0103541d0010040c1950765004901e84030b0a084400781003040391821000c03a2a48400d03540030084131700401c0ca074001848241803150010351541b40c0c034052202041004160803994070f0700c91000000038440035182c280d46503140c14a88941801c85001036401144110114420714410128049078400d641d9a880c0a5150045054144640380c154242042240c14021910714070074001008070358450000050f2811401ca400707800c06000e0064080160000c3c051002161599140305500c0342040300c0d200e890013039180c0012180c182c2e00011801510001c044481004000a141d620b500c00d940c40f50b0050303030744204a48058075000c482c1551000038460074801500f040f2030201032440c0c80b90502045540600d03041c1440d00304c810008002503626a46807580e550014000325203034003224 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 167584793 1250 167583543 167583583
    0xf0a06050a0807090f03050c0a05010c0b010e060301090206030a23060a0b030c0c010204030f110f0a0b0d110a031a0a0e0c030702010e0715030f050108070510020c040c0c05 75
    0x2200140080c000e001800051010b41c07000114024403c11320100644640f60080c10059203a017402651140d52107a5280540e0b03903072074003268640c050707203502c0348080d4400c10400c800da0825002141035200a800389415649545900d00103030748a0024602c502c1d44405c00040308643e0b006a48001c40b1056040d80c918034040381486103a480303032000c2d8030643d4200d0b81080d580c0e8548092202e254410086107000c154400704001c400c0100c0c0900c4c1c50080d9014079084220520840c04004104545640d03107944000820000c000300000500642500300903032200007003010840325446902d41c003011b200b000090350340940488031104240c0308011900c043e40e00d818a28280f8540c2c2140c540c0140040140303902c040005100280b00350030403000018038000f51401c841e50f841448031045444107440000c6418010700082d81051442118101c4600d40d004200c4545020144a9034805001c020380860158101c0c08800303450f50700071400c44040c5591001102c0c40035003030860604501e12062114020300f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 167586043 1250 167584793 167584799
    0xb0603011a06250f030c031e120513061506110105040f020918030f0a0e010507020904020f0103090206122706041b03120801051c0807150908030a02090f0a 68
    0x2c1d210658480800d10580c2e002640410001006070031071a01005000300403070f030100d4003003503030101004490340d101c0c0e00ea031224082007440751401c43c0d2440725002d0000c0c0c004c8040f41c9051285030880f64203d40001c0f001c0211403656100c00c0300f5152940106405100b10700801c00c10180c2c44440d40c0207000c101e8000700098105596442032400322032201a200ba001d480c0411000368049a250401d0324a9208495507401c0c0b000184a00c0d421485014022801c000f840707030015406003040b40c50355913000304040f920341c2d61136081210781c0c000e50b8100da0405940352039034001a04c0c2c040c0201005c03801e080311a91213242c562401d40c1e51050140080c42c0503110f801c04c461080d07000080070368100750b00640e940c60350400c006000c114440781c2c0c0d10280221304403114a0380481d401c1800d5906a4105941340102c00708141108040000000c0b001064140100034110200b03114034200280102529404140850280c0340c107203031900107640c100c4515a00044140e231030324090750905001c0300e00b940c044c0340704d0345 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 167587293 1250 167586043 167586049
    0x50d051206121c0306050405070509132d0609060b09030a0303050601050d0609150509091b03030f040e10050910050603070c1202070810060b030412030e0601030b0603011a 75
    0x10785202c0c091905001d0400d0446070600c802d1000002807007080c0d0040080c402d0040242c0924402c15000364070b0301c804512058403510494030305400281050445084030305e034030001804544003404240d00001a034005002c00406540407400381d4160105110f414403041c1021113609910000c0e04140070007c9002c5030710040742100209401d4100001c0760764a010050783c3c14415044202d504a1a0020200d00000076503c212094400c0000d5110381940310024400702010544410840758031080c030944003509102d07200b4134086000f5095a080031804944020b00d5007054011841071011031701046984225441240b004200449081e80241040e203005080080640134150040d2070000005880328000c1c00d41881c079a034041404100048140c000a480b1f1700b440c021124603001c1c80c00c0d0fa0040082c1c0340583e405503688a240c070f510751b89403955074440e920038442030f020034940c6960441000718402d000181c000c0d40030304020074035031601104150844113465003011503030090b0740e00501161 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 167588543 1250 167587293 167587327
    0x901080a0b130b010b0c100b01020304090e0a082107030b01050304030818120406180530061f080318041a0607050d08012c0a020c0102070f050d05 64
    0x7900700041c6001030b151115050003640d0500c02c0a010116074200028003d00d10b8070080c0b0300b0418110507150b00702ca50207241002d8500d10080580140e01c144030030f0051801951100c0c0000c480c42c002c50310407840d59683c038885604049a10041c420030125164003941c010340c400b039817055407072404000d07004024001901c80c1c0805003001c4d0070011811300052f031404030b001001c86540018821542240c81800c8410241e611601541c400130b220074180089884840c8429800d8075001080507520f501030f00c0c1c07103140120382038107006186005c03807108415828040c42590f00a46c04061484201c0340351b0604800000155403129081d94400c10610301d48031180e45200310701c07413401c54001c1842c0312880c8801010035400315030b05a0180e000143c3c1020003000003443d00c11000c0c1034403950301c541e9880030a4407040d2001c16400c003000303882d07071003035403801da10140e00c650b025000c0e4100600b011204000e0b1400c81e009081c0071950540c85050003814080b00300701010124210f480d10515014100407030384264 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 167589793 1250 167588543 167588563
    0x601030c0e1302060d050402101d0607170d09031b0312112101090b10050d15350c030a02010c0f060c0903120206011d0406140702030408010605090108 66
    0x500020008108954080b016100c0d02c2600108042e4690051000403402032000365400c82c42054900c1c90302111500030300e10b20680c640c0d044901d0810041c5001407014950010740c080b603200702c0d80c080704424449147c01901c0b25034401c01001412440c1890302a001400d04a2162404511142c13804000703907200c45c095600c0010a6004514114101810702041c0514075200200390b520b44842d08240c03880d030b1904c42c12550382107010712000b0058002d0007056690700c4a8140001d10400601c840f4400d560000000541402d041d81e060503607490341b10305041c540d0781072038000654103c502602840c4640050602e245168042c0c080400c400001907950951980002d051145904545080c8100448500b82c52900090b040c408047c1480e801011301640e404201d079807110a2000340005440004c20343d0507140700c000780080c20a05610a40d8424100610407150640c13290705544000085035017150145217103130029170311541404444c509540040c1c003c180105500401001910b00010b004420303 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 167591043 1250 167589793 167589809
    0x31f081b03030322050705060d0b03010f02160b0c04030f030c03110c031e1002040602010203041202010e031e130e1006020115030602030c0c0106031b051008060906030102070203010f050a0e0601030c 87
    0x1a013031524205080c24020b91003036a000001013400d0110f0241c50b00100b01c40d030301c210300800c518080001c0f118100d0092001a207d0254500740c03c0c03000854202c40303141c22507144c00c207076414a40e980e034030000d002c7e0012400b00d0001e440b200040c4201070b08044101c58000c01d1401034500c81e5036000102e076980c0001013082000111900380c0e010300304018448208640081c140030340d83c2e1900d0b4900030b4040d5206440484404840c84004078030759106220307500f61200c482c00514640300c521005500d120b210400340c0c024442040008640b0b120030208510000c1010141d10500e616202041010808a0350b0142065906200500c212920403481c503a080e030394000401030712a03d444039400410700078465516074541c43e000000c01030204160031801d200b00c035a00025582501c60042c051070407a41c90700e03180420300b4400860600c0c601242a140d1280c0050300050403d041900002c5c20b49810360301517101150303641d0070b121a20a941c01407500d041d14420040510b540740d56154404c07586144039602e0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 167592293 1250 167591043 167591101
    0x1a07050a060b010c050609060106080c040b04050f010e03160608060a0501080a0e0109020907020606041d0a0f030e04110301050301180201020a060b0312030103052a0a030206031f081b030303 83
    0xb6180e0702480310220060740150446007a8a0b001c40115620402806941d02155901c40021508980b40003101c042e213800c01032042c00c00b8070385001d0080381207007603035518180a11610310b00c071191170810418151402d005000b800e114604030001d40080c8001c0c2501c0d0050218050600c40da076044807041c2d822411180000a204103c0b43c00c0900500711400300942c810404428480c82e00e078000350013401148100da00b00484406a002c094842c0e242044003d4260049040d001c00304480c0c81445040d40d0290403c4504c0c2e00001d00010116650303114604469640440180620309091003001541d045001c213040c07142c209a00082d6541c044c541c00204820344403182e840c210388091040399442c5044220242c4c99585a2501603250300c41c1c900d06101003888440503800a2a004200001c00703c0c0107070455a8407070840d024028151b20040640c5094900c3d9001c03540148030805a800041a400d0080c054001081880141880d4102d05041c4294014410301520520300c84094124110044604e1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 167593543 1250 167592293 167592311
    0x10050903192c06040803030702210a0c1101110304090c03060806090c13060e040f060b01090302060316030219050408070602010501031e1104140601030c050301030f14030c161a07050a06 81
    0xa0340f42d1007660051176036400b000c000d01074465000220101e050381c0d501d624800764420400a03144c0f5020308651440000c0000c040721340801c03001d101c0c505070700106141171607440910b5080c1519540c050360040700d41a907a0364000003504c1c1d0500c07a01021303200400c040c001c0d60801400031680d921800c1040c601c07800701c251500078081c90b41c0d40200010035028501044038645400d08200c0484641003d0302d59506281c10341241d0342c840c16407407003a650300900307060441c1c80f01c200000902e00303000c8900003415420001340d50803c034041d001030b5a000150740c60382da0360703030500c2d412608001c0d80e940240107682c1040300500000c0c060408101c1e06040703c000041109100c0d081c000d030032114665100760011702e006009580b40c0c9280520901c03a01007030704d017405404146041121680300901c1b02803c0112100c21110004028007101d0409000d10f1084905068041e040e26080200010341d00c10625003114041042c6000301c03445070481e070521000c407410580b180d11030340d0302c1c0e007940c20000b03113080d6a85001c5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 167594793 1250 167593543 167593549
    0x15040312080c0d050c070b06040b15090f040912090b0309030904110702180109180b040803100b0309070305061003030e2b1a0a0b1c0510050903192c 65
    0x510714400f8032500c10f010780e05001402419680c040c2c0c0d41035409a402c44001001e9040c640120410803030098111150741003100c4000d43c440d00142e4840c1d90103041a00014034a595900850040a004c5d00080658100308540540000030b20752011606040a10400025290210036590340a50540c5c0125460a0a0401000522034800c0003903200043d040401c4030352407408500e5058503e401c0081026548030792200007821010040105280200d000150021b8050070207550003501c19070b4021422629800300708025001140c1d4244140c1c80100b08000b401010462160805100f0740300d0000d0500f5510000d00ca0507005868034059100c0340038181c001040d101e403d030030922080540d945000b640e8640350780c0c180d51200183c0742c0c2c03a0080b404103040c2c14007842003000ca180d000f8034000c2004c020350310084281506140a460900944641695905072405900d102d0031111010359501d2110483c41d09030b241c0361514030000c001d01c03201005e801c906000764050030139401c1041d0f100300038440400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 167596043 1250 167594793 167594797
    0x6010f090315090804090f0e070b04060c0206040b0c030c160506090415051306030b15090f220308010617040512160501020d020a09061b060902030f06011415040312080c 74
    0x4c1020030300240002e4000321661108480344014035003404000100b0408540c4c44c1c406000e41d64141e0b03002c000400c0114001c6011701c0101e840070309580c3c01c0036950b4150764405d40001e03113950b803030350000600c2110308001070140030418900100c04013007060a081c0401c1d024021111858000d6545524aa9118520610b0a030050a0040c00c04810140c81903034000508a2440121000008c14012a001a111000320f02c0107850103840081c0d41d6886005190707048034054641806143c225243e4100b40e501d41071030210140c040d440341c2040d54034000300113240000410306010600c84210070700001540103e01c1d1074614014462964440c14544101d9a4680703400400600a40c07000440300741540b0726401501000105807030340d400035542d801e800d46c3c00500e441c00800c0500313404011840059030340c0e4030103800c46e4009000c4507841d41c5850f042c40d140c140300303030014941060b4113142d004007460304045941c1d0b1004c8210919082a01e1a503840b803408400c0482c0800b80300c0b100700001c0e54080300d541 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 167597293 1250 167596043 167596061
    0x40f020102011d07150e03030d0c050412080322050d0e01030e03030117060106260411040216050d02030f03181908030105040501090c02300c010b040506010f090315 72
    0xf284800e0b19072055900d5581e00c824031620150b0140144210b02d024050356a0044c0d005020340507614006013140d0740c4000308801c902c81000c1c00001d11000c07074800d10f6400a03451841c8074240c48ca588ac1860021a80c42500f100c0b2941022500c40c00300c5000036601052100c600d4007035041c03200200a2140060b0040c00329895807045620002c8000110b01200d074001c1c041c80140c40003a00c00b143d072128000c8070f59a100d40008124041c07520804041d4020284c0841d52250050486c1d00040c0740801c0001c0c182e9006052024042e02c54500400910005000d4000c0c4015140002c5183c00e002c0c80f0080d2079404010024552826100c243c84030b13a20b8180036540c200c0940340980c1c0c0a15091f0301e40b44070250420b005050040f0b10300000441c020700b051003009481181d6400421511240e40801c0b140a0500c040f400601441100c54000c40d42c280300c00741c45810200c03000401d020141130180411220001c00082c104913505401245480d082a20a0240c980001c00c1054180704d140e401005030201d03130 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 167598543 1250 167597293 167597321
    0xc0f0609060c0102071101020c03211902100e06070c060f02090d0c0608090a150c02070503070602010b010e040506180c09180108100603080405010513081006030b10030308040f02010201 81
    0x2810b5400c1000c103500800d8410710130304035040d4000d480310049a4170000e5280311609175000304072080304018540f0410603031f02c04030140645480303090888103041c1190555000090788c0700c4410b0340c3c240d10080c081d90004061000040a41d841d00c548010403075002c01d14090041c5540322603ea003842d0746501150030247c8040c0c214504180503140001080348540b1852002446040204902080105d103c500091b00b000118408a6541c040b0700000c2920000d020203601c01e407040042d003500c0510046006101c2600009220201400054046441601d40a10a510340010042165150300c0d11001c03011100500d20210b40c0c5101039583d1611402c000700c2d0b404003c0079420031502201d081824140c50707800007502d40c040080c06404068482c20b010013020f455081c4010700003548640003901048a24040401b50f4542e5100d0141c101004180c41503c01600c8000900c20b100342e10346026040355402008800d02d6295440040254038051b2000b4190000c0e010a001968800d4200800e101000c1d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 167599793 1250 167598543 167598547
    0x6070f080a020a090308071b17030f09042003011a0910030903050f0f031005090405060a0c0e060409061412190201110d0804021215011406040f090504020102071203020c0f060906 78
    0x1608020f8248c040c82c245503118200c031707544007080031046283c1d007000510342d0000850420400c018020501e1b01304081082d0016234039001881d0310f40d0b0304100c000c0c015480e18400c0740d407941403544000007c04050719070746203500200110170343c1761100c1000d41110081c500d400558a0b140340b501300c5451080c0b041c0c3ca610b8010100350b0000080541c2c004500070303c40d03406540e00041d80d80342030104102080f02c002c1c000350090070000da01003007140c001c5c10622440b440c01c169041c1c014000a4555005500001c50303090342c4c0c0704144242c2102c442640c0d203482080350a8019510614111039a4a41e605206c4103d1000001107400716400b07240c010000007240c40540e071030304040c0c000040410078122401d0b446010500480034503000701107101025005180303a01f02d400d80c02e00c034107403654050300b20b070f07030303500044100000601d4010803d104c0d000b4101c4068046040d0900b070000a00d400610340042e04030040c0b80d160100020740005a2504483c03060741e10508031080c40d000145c41c1c2c00b41d107904980000ac0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 167601043 1250 167599793 167599807
    0x41d06040606061b020904060b01030b030d02070305010c0912082a15100f03030e0d05010212041a012411010606031d0304080c09040c0f03120206070f080a020a090308 73
    0x1050b0000e00c2618020ba54404040c08034034081564020304400280d04500c1c140007080120702c07150440d40902a0606000c41c080e241c490100c0d1074004610346d4400140c2181c8001d000300302080c02049141c0c945c0d464800a4181071520303c0c00d080340603000081003418001149685000c2240b04210311414819001050080310b030480ca444600d40c505000c0321030480340020b01132901e51034000041c0d88007414444000c0342156008c0c3d0f071540640f00e406600c0b42000d18514005142400180117800090390140f8070790600e071a1a0f8401108680f4440390480040f00600540d101d41d82c600d40c4d640c2c5c1c0075801244140c044201660701c1e140302441e4040381d5080c0413010408542603000040c1181d9684082e03401440340d141c0c819103d0081d4010303400550030051300a40e041c07410100d00e07a00a0b02a100c00180c903136498140c40c88801043d4400c6900881c58595040c0c1c09805009071903004915040c0781c0001148003a005100d140020b03e0700d42d03175560220b22074505501c21081d40c17000d954002c400325a2492 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 167602293 1250 167601043 167601053
    0xf080703080106110106060509010c1a01080106030b090c100f05070507031b05040b090c03101d27060708090709060b0c0c0d0b06040515060325030902010905041d0604 73
    0x14240103840100b0094030306540103404c14441d00782160350658902e420081184c004503140080c1800c00e0b102011005440b41c15408500280d500920a48000040703051552500000524000b8540c204503004201d9689541d111020201607541003441e1540300313054003003405d4640c0c0c054040080c3c280d10038a0310110800040640c48040b1031400c6443c001c489545000b000f041d07503031400080b0b4100c1c103404046030341d8070b2514020310b400c14502911200c10315101c1c0010500c4124004404949a824400784a1064440c51419032207802c01031514240f4000d08410076540d007000303050b010401900a0014040a000780004400341c0500e12041c050180e483d0210f86071500030301d2040c14580603a00004803d441c0403c8107041140c0e1010f413841d143e0b6181c804000080500809060010300d030716042c43c040f0359521700103500c10044d5009000c01c0000010070091080c0054200c1024180361403e0503015030380041a50080b1042164042010b2807102600003400c0a00f50300207815100f44818031003085 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 167603543 1250 167602293 167602307
    0x10507020f07050f062203140a110a08031c0b0402040914060303070302060a0b030a020d08070c08030f0403140a14030a230703050711062101051008130f080703 70
    0x2401c039100b26141940c4a41c10412140c801059a95110360200300554003040d6078100d04804080d84005105007642e20b89588081c2e0a0103080c1d465503410981c032a1042180c2c0d03040c1c5201d00307a0141c0d103e00c521820103892079075030303c0380740003942d958582c181c0b0400d4240f0345500812942400688107549695880306004040d148e00c0f070354600c49807668000294117040020641d040c280d0180d0040485450b01100c000044c40c15100298050047e860b100000d03131211071080040314880d04074540d551000b4200300c00070380a035402080294000700f00c05103a0200007825603003030b45e40241d88072134040b5003010854507281d0042c40c01022032100d142d56840c0050040050100400207464945200c0c2c1010440e64001d005036411300303070400c01030240304082446000984001c0d0b1040c4600e040c0c4881400015071580c000328044464210005541404044401d80007401000190341c0401c44e0a020a006400500000c0c00300c03c408103558040410711542030115040d1541000d0400d58590490170700508503 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 167604793 1250 167603543 167603563
    0x40f050a080a0812190903090e090706020601050f0d02090702010605150307090635061206010b040e06150705160510081b040801020c0304050a060203120604051801050702 75
    0x302004440050340620215694407056482004245411442113441000c0070024140110899407540d08100500c3c9070711036445001c0c000e80b40c854030a486c00e40d0414500c0700045c440c4109400840c6c0421400d500042e456056400803140700c1c04500c51440400c48409d80380d40f0103580030b9003940c14804104d170194403039070a441c01a502042107030702c519100102d41c071040d0340a80004013104404c00a5900c90040c1c0300662035400307249480300c507180600c0c2501c0881444901c00c00c06000c01481118036041c000d0140e03060910010304043e614014881c01c0070301507449401c03440f001d000009840381d540c4142025154001c111101e803a907405d420a103555101800b41c042c460128000c010490b4a01100200411695036513590519511085075800504c4a021001d0171008140320104150b803003030000d0810111010010341d225407600d02040a00c0c040d03030340321205640080000526110014140c1a030080707081d50042401d81750701030b541c0c031442e50005203640d40f5440c0100b817201199020840c0b06038 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 167606043 1250 167604793 167604799
    0xf070b0103020307061d0d0f05150609010603060b0d0c030b03070603020403032d0e1c15060b030106090306240b09040c05040b09120c09040302060a050705040315051902040f05 77
    0x3d5071121020b03202c3c450303d200c0e040306e01e4031504007860039460040c5400090310310a0302e6280d048512642d0f941d2402445601c0480e00782c000d11b0410017a810210581ca00414042c64144000c51800794005480d10035590ba5820fa551a01d5141c50000e0003a080b0304400a80a030481d101301e40d61783c00041c000e4125000407000501400c507211401800c10451000e10308041c10070b00c1d5401181d8006440042d10050380369000400b000d1080c1c0103911000c0944010741c0201248030358000100050710458680350088840300c0c406100600200c0d5008082d4800d503903000000140090000e804042c4007213200c2140354007071400f10404507190f00040007408028000307440a200808200380e06075000e0007a07000c2d14110501c10b00251174607280162079001801014400c0d200c0320001d15010a40d002c1d03040b9005d60142e0b2104050141d280c0c00d0f44200f44c0e0223401d61411900349425607540340d80c40e500c0d4456070340f045a00c50022841d44800209003900305521100d00f195501e0740c800071100c0e401940d00c00d280c4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 167607293 1250 167606043 167606053
    0x305041403030f030118060506040f050306060904050618010f051003030f0309030503070c020d02040e0a03080f06030601170c0306040309081207151d030c010b04110a0f03050a020f070b01030203 85
    0x80c03509000007030719481c640c04080c0c1c50843c0e01389941c1e81074000d180c003120707400319880f00c00008039601e5050007007014010131429803038507908140134035207030400207410b2038001c2e940b110810010400110b400e5401410541000707420b440c8034030b40140034000e041c203070f20400c1d4580014003030080140034180c01181e00c02d0b02c0d00002ca0800f8031040e4101d07180700001401050f010800604800d104a000211a520040c1480c40d0f048035600030404603105400d114055500c20050001855002020359502508441c0da040c1030b450460b01083e100c107011310a0301408420b120002400840920049070f103240c2c00341c101c400c5c0b032409041c02007401403584207a10840c041c00c80c1d4810343c0ca03c140115455140c00c00c02811344502c0848819004050800c88651454400c681c550382002042c00200100c55a80001244400000c0100000c0700c01021880c40302041c200700100700145c01c11200ca030f81c0c0c0854100000c6950720001c800c0064803900d03030070140e2110b000a000c01008004c0d0007883c140c81c002e038210b503 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 167608543 1250 167607293 167607329
    0x24060510020a030e1c140102040f23010e040204030605090c090a15050d05010b03071707051f0804021903061b080c07080d18050c03060703021312020d0f030504 70
    0x10b030b01d8540502010300001c800000c15005818651142c400021203a4012405040c0d50703202c1c6501000c00041350b0031036940000e4100b0000e0701d06030f01507001e0a01d10780d0300c44082800342000c00d00000300722207450502460104850960742d581d4140c0d8011a00100d0909c500d140c808041070b102c080c1c20750301920402480d80450100600ca1040c001a103104a001610903414882041082036941c00110350035074940444020781d45050005000030b040d0780640d00e0301c0c08421b0685070f0500296400c954014400c0450f90300ca680460072620607402c01c3c0f824513500c01d88540c00400c640c1c41402c107003420380b414154000400c001c40c0c0c1d4007041c400d020050400007500c02e012000c4603912825142109403003400c0c04171030003003020700005151500c00ca000000305602c0400e062480304a00345030a541d0b80c2c0008205d080b56050038000d5650058203032608625000480207518400701c03c2c1e000e280d507205449101042151a07441e10000c503d500110049a80c402510b401009944240a644481d180c095446 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 167609793 1250 167608543 167608547
    0x4020904052518030b04054608030606070203150705070201121814010f0f0b010e010207031e030c0212010b12150a0b04330f030807080724060510 64
    0x80490f0351082e100b080145461901c1e4036442c280060710980311401403266001c8207020324081300700010504000d69040c2040c0d5251460790707510a0203110b04400c0034000c244000f900b10b0301140d0340400222420f50f03c0c0c100500120b450164110350304ae8680d0000000e001070b59030441c01a05203035100b6614404003403600401e4109590000403410036002075031181000054118403480e0354012142c0000030034503071000700303401075400c10200001311543d40d04c4454525684000c140201701070078002801c03820310355034480701601d6415000808040d1050891810507224071541d0031600e80003040d8010160780d106115000701400c20086202c2c2056100f15501e240d4081410202d08180102c185c46130390302c941d5160040c0164011581d48282e440c21085452582c06d0b014060310b80c02401c80d02445440041d45650000054101c285248030b003010130400140500b08644002d54002c49554854015150200141040340720402e2120080415100852880c0e13100400300c40040310803200c582804041 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 167611043 1250 167609793 167609807
    0xf0d0915020d270611070b01180e0d0801091109030102031503060105030f100f0e1009030807052b0908041701050112081803070503010e06010504050c04051c02040209040525 76
    0x40c01c580203090301c0c0720a000c14165170044c071117015043c00751032409059035140080c9507000d800c0a00350303030301424524501d00001e10070000d6400101d8000e04401129a102400d6900e05204d48140139440d000b801842000b00000d41e500070380094020b41d20390900114081003142c800318118040d206c1c9000003e942d00d8001000a4030340070b03280107021a52140f622210141c10394140a4524640b1100b424108040400001d8115401402c000801d10f0140c82c0c02031149a01920003000c01c04140240e0806261240103121030034002000440007030071540b5503070701030a80700c0e001070500c020100d00040d40310640e8602c4160343c04900700030000f980c1c0310f80385180800c030031550103440d118040c00741103005100e40d08070769000b0400404407092299100002429a05000c401c102c081d0850f100400003810300c1c0c010030f0b400c075143c1d104141c1003e040c1000700b43d000c142643c41c200347c0d8507031415980a5480d664121000171070301420034046444d0004502000c0124034a4224118000e112120121403103400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 167612293 1250 167611043 167611091
    0x827030c030d0b0402030403091707030b0a0c020c01090605040605031504021306090b040b0f0a090801050a022107020604080a03090f03050909150a060e01030f050106090812030c0f0d0915020d 84
    0x407025003007801c125412b50401d9400c8905500c900c16004040089003440e00c010f845840c4d0080007240403c030600c0000e0418240030085414819881c006000040e003010070b035020750300d07203103441504c0b540c8016094030016400702c2541d4206100269120000901210b0311055804c02e45035100b10a50742e5112401911a0388156140108140300701440b801d91500181402c0010b49403071501c0a4841a0f250700b116002c0c1c6070030b0120b5034000785444803106100d541d40080d0400405514640c44c0c03a080194599000a000034545240081c0004a090180d800321010540003001c1046146441c40d0242041d4825071115110380d12010010f00c603074403031584150a0307a80140440407807600d4a4400c0d1124013517816941e041c151511000c0c11a59003900c109402442e0580d01e55040c50314141c02c0d90f0038444c8502e031445045500b041000b1110f42d07070f1000c5401d40c10b000520503a079400310356031040c024006850005e2150150300748008101c0c6207900a4107040a95200c20805256110104103d1650f050 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 167613543 1250 167612293 167612297
    0xa060503010e13020f2d010806030a0311120307020105070e060a02070303030509031e041406130e0403120c021606020c0310050a020f0c01061404020a0827030c030d0b0402030403 78
    0x2400191040a540c2003c004042c4090305c1e034010018150000b4100503040f000c018240400861400c0d0030485040c00354400a00030300342848681800004241c50f100c01c01c0002d014006c40b800c800107208810030803101c090345107000154030b0f0b04100c1c400a020b010192207138000503640c0c0ba4404102e2400d80c0480f554038810303070028448107145a5043d8003070714005050030650b0006100004100011007041c0b541500700c0210541c0d12801c1c0352090090740c5051121034055002401001c041d480d070701d400d442c10b03980009108000c65035030303203000c4030208621101542d1b2681090340d07003040140c001910031010b00c180c0340441c2c0308a03140c0c10100e03680c00008500d00c0d403651095641214180f45948100e0304046400005450014009104a103075402880800c030303da9510442001509203500720403100d5802200c0135840d01c040007000410038500640956042e203d80340744018446166081200350544003002d91740c87d0840001c2d4151650050640c00d80200c1c20700321401c09a1800e0700c2103030f128561503 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 167614793 1250 167613543 167613569
    0x60b031b09180c041a03010e0601120609060f090302060405070b03280204051008010e0a0908070b070e04050a0605090603010e06190618020315030a08030a0f021e090a06050301 77
    0x1403a44000c1e04040841c2d010402e00a54a0501c180d403144d010711000513446410507000441d03040181401c42d400e08803030100c203802420040c003103003a030707201d001140c1e540003400480d42d100b113402c00030300404e13800410300041840c100f484000c164021980364401d034040c0b015282020313583c0080324031500c0212041121841048124144100591040343c500000d03030382c0050800d0340b2100481c0d00a000f99070000c0100c3d180340010001c440c0b000000580c0903244020600c8007005955030010140601c0700c004010511203000181054452105c00840300e400410520450030420002001820203016642c022021800011624241406044401944200288055239400800b0000d50700007492030034030984c0721180041e44081d0402880c001d282100d42c01030707503400d03d450644040041690340074080c0c1c01c0981c045000c0b0b440351090f641c1c07101070414041a900199002c00f4001d111381c90200e003d0940da42d840d28119150030015140481068980c8001d290700c1c1d420030386040c0400d00c60f4010700d001c6 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 167616043 1250 167614793 167614801
    0x108060f190c0306050d050a050f030f0f07051603120e0102010b03060103020d0c0306020307030c030b01030902090c0a050f03130506060109030b0105060a120c1e110703080705070f03060b031b09 85
    0x203580702e900c01c019a85000903c164803100002c800301031180e001c1c2c1e0b480d48004082c109000040c80402c60a9000c40025440d00004000810b840c0c01a0100c0000c2200040391601c28800284040c10641d0000211000d15680f03070702d0b2030707415142640b2021000403420455540d055005100d060200f030300080040003240c0c65582089118601c11004640031400c040c4004005030043c000f8501419142e1004501c10b0303014840103040350300b140b10803810181446042030250300c1d1201c03200d4100381d0050740541d1700c81b001031302601d41d03116003061201402000000c020720300c10070514846480c0e101e041996407079119400115410180ba0202038048092900100001d160110040c001e07ea05070602c1301e07a10f003402240030700300c4040110450119002c1c0605068040009448000d441e540381004d410716007001c01c410344e640c5140d00004102e440e00040034814030030104080c0004011603207012041c80c3d00e92803c03601a200c400741c090301910580861f0750400c18a540040b0900328081e00d00c2103250f40d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 167617293 1250 167616043 167616091
    0x90603131406240d080d1d07060c0b0a05010e0c0706150909030206072303151f0905041b050a09050907050403050f070503070b0d11120108060f 63
    0x1445801c86510140600d01c400ca00401d000e601d11801200c0350241d500151407191040189030300c1c610500c07550420605a001400c14010b440550a02a0b00003c0c401800212800c0f40c0b0502c604501861156001c001100d6502010303085545102e40d00600c03041d1103100800c0261402809805000302c030ac01d00107045001c2d9030020b04030150060307002244080079201c08040310210b80d0841c0c2c541e00e441e554800c090540400040303410240520b080446014440b00007054101c02d106145425a400000300b0070f1080407814202c2c0004005002c000c0000c804690040f404400e41586000704007603480001e85440c0c28030603221201e406410418000c0080c0c28120b904d58030406061003404a040008141501e84000082c49018103403501c0741d9035400c40c06d20707500e070000c0040e4540c00e1b0f80c41600305204d80d44000c20604115440c5039081c030345485144041801500f134400c080d142e00300c404a418040b01c00e09000c403504880f05a001c2c1c48150700c80c02c00d0900740308801c80c0c000c0b1142058100d8522000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 167618543 1250 167617293 167617321
    0x9010c0f0501020909040b01050102010e0a0b01060f20011b031512031101092a140909030c060f07030b030318090c07061a09060102060702061f0e0702100c05090603 72
    0x1e104100040c039205801c8000345070300c5400d80e02502c142d001b085c0180300325602407207048000001031004024900d080e07615161020014040c00b000c1000203040a2070244c081c0064460484034451219800224144c0e102d0003058600d2103410800c5503140b51a443c1c9002e48200d950b10f1405a6100b01200d00304100361034054941001181040f85000603800980c00a00c2000d091074401c1300c0081940c98208603510140c013980c154008298042c4200704203035030030340340b42010030601695140c0d00d03551007580c024254040c030484d1032000d0040b5800c001c0364081d0708803103e1141d8a81d450400031110b4510615a581c010002d002e84c0c0d011160501e024280343c002511580480b40070611403a00041c0d0780d6110985480c0d00400c0a40050340d00a80400c7c640300307900ca68811020700c01880c0529240000a540d894040c4c600c59040c00711120140c80d50480820310f85c0900700400b84101c1c1410b00c0100250342c0c0070070765480c0c11814940052105805e100b10112401914000c0225007075440f882140c641030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 167619793 1250 167618543 167618573
    0x9101e051c032d050906160b0603070b0414132703020607171503031306020a061a0109120501020d0e0303091e0c010e0a080109030503090d0305010b0a030c0207030203030c01060807050609010c 84
    0x80d0305100210b10240e10043c0300007c1072055008180a013040010b0510308601070300200c2c40e41c40240001c0c00314001400600118240c212403000304500b0f0000c5480051107000208424030644c6d5100080040c6001105d0b403201d03100340d00b01c541c1580c80384011940c455440e009000d10800d02004926049170200760071030300c074070014180e901d040140303880e00c00e0181d0b0a41c00100581c005195880900403144503c6a5240307580c0d030064002c80c10000001d001100e00c1c09003080f100c000d01c4545080c0300e4254141c9100c00b003143c5041107580c022410356540ca4004803203003201c5200d680000c54690401c1c003403003d4000d0740c44004002c0c00d078002006494103509030300590703004042860005042c50007401111161406500e4186d038a040000c0012f01b050140b17881c442c14503007041e004010003403051044482d001c905180000d0b07000d0aa0f0b10880c1003280652000c0d50503c0042440802a9010341c0604201c46d03510040340c40300d542e1001402014054034a503603000c40c90348000d040c003082000c00d1521754 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 167621043 1250 167619793 167619799
    0x10806040e25060305010503010e060103031d040c0c29130201030906020d02090111030307050406050f19020c120f0d11030c07090605010e09101e051c032d0509 70
    0x22030750600072610100e00c00000b00e18081c100e12041040300540600c03507103014000640c020f001080303258812035640c41062000904104070000c0c82ea45c0d040c540180040c010318028400d02c040c0034003080c01070100c0180542640c2e0a0b101c2c0a401034400040d24544001e02d5030300503034000c503954a5102080000e8002401d905050301e41c10f1800002e0084e10080c0030743c4c010300c603006840b84948000100500e0045021304030641c03041051207480344e00202520700301c07000f5103822a85d502c1c3c04088920140104040b402c03c1c814080d121890454020420541c006019200400c441c07420f04145580c4030070b203000303000007500580c0703503440010302c560380c240c9200c941030301240d10b04001c5600f29803610b802a8804030503251b4030305082c415580c2c06507071602d41007001c0300c2c10380c00d50404125a50040c4014452900042d01c000c3c0095920014410b0b110020800180515069030b444821103000d500420003c4000400d001103031454101c88000c80c440c01412090326100c1083c1d40c000c25140c0b54807180105034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 167622293 1250 167621043 167621053
    0x309020301060306140f010b03060d060b0405090601050103150608012d03030206060a0e01141018170c04050c220302060304030c05010c08010501020a02010e040f02030f10060e010806040e 82
    0x160310240512801507105150005503d0b0401081c16440348015054008410a034001045041d2103802a2034011004036106200c400c024503040c0300810500c503c86403c1800c1000300000c008000c51010304962082c0c03401e002d08d9070054000000d84a81307002d41c101044c01800140842800003504182800015034490840450980240d450b8880d6a0044005034070507c100200c07424802401300081c24000e46029103035045c03206080b1150b01104815000c1c0d107101075844100c4e031145c80d44607040e0300d4458140b02c556032281c0402072288079115810002c0c0c407441000703e000b800c0a201d20b41c410444500000d007894941c0300800c0681280e204000e104802210010026aa81ca801103000301e11075150700154010300d29156007560741d951a424140446140100110790300421010400740e424a042082100203000190050044040c0220102d20200406c8a1035040b01034031401102d8a00f41300d05125503410303044485500da00701050024074120045181e90410380c0040c0301d841c1c554420340f0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 167623543 1250 167622293 167622311
    0x3040605030a06120b010305150402150717031008010e0d0c0b0c0408030f0a0e030105040302060105062d041a04030c030803060d02130510080307020d081b100203220209010902090103 80
    0x50380394403030344c0040c0c1c2c5020b9003a004208001c0c007040506042030f0540c40e00c0d9080d00c0c1540000e07809a0042100d011040400204d4004024032804441d0880c5501c802c51900d03403c00c0404200080a80d02a9003080e610b41082500c2e072181c0010340d5181c4040325910080010030a98400004e0200581000700c88042880007003001102031000c3c20345802114030481d00c403000c0130b200400c038184110205000743d152000340800b04e603010540074155030040e40c0640d502c50031051904094806e0b0002a50341c00e0a03a070560130030504e5040100201e131020075134011085e40c82041402d49100e0351100400080d1041300410011b403004004d140c1c040d000070076400d8a00465008201c2128000050b03042c203a035078104000b41d044c81014690f0151400c50019404c040260b80031503840040302601801c0020041443d0340d02d052008000c124040519003070314014420100d204001c0d400585a10003c100c455450001e898800c4100f0a601a00241804101c0c0d01e0040003c000307520016840c0d0415848502030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 167624793 1250 167623543 167623559
    0xc070305030313060f09051e07030204110a0f05040f030f06020c030a08010509070c08090f03010b0a0315110903031602010e22050612060711070909060b041a010203040605030a06 78
    0x1e188203801c00d0b00f10300f414820078039040e800c0383c0d03203d81040b0400e131400a4140210340c3c00070310140c882c25130040c0f4407002d03500241541c2c80d0607000e6000951241c00c01410021141c0c107040944039000340d0b6101c5443d0143c865809491030300982c010301e4103005020000300b021401d801d081e910860b00940d0010b24020588a03000d0071580098420400f20fa016001005607042070403c4541c13000d0b103442c00d011007190940e1860b07510310030300e06024420718010b0781032401071b542940a9049080014801d150070341c0d40e0b2504402e15020b00446185103803a01503000c034000070081c03c8440b0004020301562414010760440700000c041100c1c141d040081d0412543c2560301ca001c7d14001ca0500204540c101340401401041039440081c45140501c10208a03250198000190141c1044180c180060343d0f02d41c0390522441c0c0007080d80004065410004c0050074400e00b90f02c0307031280390303410344d418480c041c6a0480c0342c0f5040c3d900c020040c0103a100b044100545071190340595000521410702049656641ca40f07 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 167625899 1106 167624793 167624797
    0x150f2403060301060e040b1005010f12051008060c13090b0a0b1b06040f060c0905241603020c1903021302070503090901030b16020307050606060c07030503 68
    0x41081e5903020f400c130601030315a58030402c0492a0a050062111030165104401c2c4d000c45034004c50f045d441400e0f8103c0d903a5040d1100310469034101020001018002d1040240382c1807403201048003030080c8402801001d06901064a4107100600380030070402960041030300c0c030b140900100e056142c1c10590b40031501801c002070340b25a000c5007480c1c0b08030281002500706015083c20801007007240700040350664020003080050300d480f504280c40e201400c1c01003a9000d100c40c1c54101c50300107001070702e141344613003025120304100046003004508200400c044025811210019a0500300448200000105070000b50392162946c1c01141d8911100c241d000ccc4034076000540740702481030800c103c03a0340c0c2402900b451542e41e984d00b000e208455044c0c40310341c00e81d04c0c00c50410102c50320000640c0c0145130040c015103419100c8500f000440e03880324039402a03900034844000003080003400 = true := by decide +kernel

theorem cover : BRFrame.Cov 167446043 167625899 := by
  have h0 := BRFrame.cov_init 167446043
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167446043 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 167446043 ≤ n) (h2 : n < 167625899) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
