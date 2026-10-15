-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3976
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:13:30.301747+00:00
-- url     : https://prove2.me/submissions/a722ed9c-0dec-442b-8abf-2977abe15e4a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 714928057 ≤ n < 715107913 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 714929307 1250 714928057 714928087
    0x6071a0a0204050901050303040b07020d0c03081209060906040302100b01020717030309060702010203100e0402130c03020c0115030c0b090a0f03030305160806180a0908030903040321050304030c08 86
    0x4124610080180e03128105420004c002070306030440340c029030081c001482000f81c1c09e07044450345501145e07212414203003072608401074252a08010800c1801040d8080a5410001030600a031040d00c2500d039180d44020f00d20b80d5600d000c4602034010780c0309482c9010300c2109075000848000040c8192444541c42d0001051048103201c00721306c05074400020407041510521107603400c10058030080d0300c2d5051030a2404000c203254001c5d08000c000c424003060031903491420110455801581c24031a00c8824007001e8000d40103600024000d50074041c2c112080c51034504048252580f0292944825081420741542034001800c1c03560050b9483c0c40200300200080c07400b03402940b02e5a808121890511b00302640021000385020500c5103003c1803010b603a48640d12002c0d04002003100d4011560b41c0e400d2400030300524100034104420000600001311404001001601d006482c452104103031080c20b0206440c807944000002101400030034002071140c007004034641c0c02500010704111107202e006c41 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 714930557 1250 714929307 714929311
    0x60a06140904061d01150e09180a0b101a041e080a060e1006051c1e050a0b0c03100b0d090c06030b0f1c060e100c0507030809031806071a 60
    0x2a0407129100c0030a2413040a41d580d5000d071018540d2542002d1901c1c0025100101401200313100c3e207003003c001914080f0304c500c515090683c40c01203840c0107601e070519442031001a1111200b40d5108200414069200ca102c001c0780c2050f000c0c201c0c41e051424504081e41e030145840c0240c1c40d03045140c00a440b64041100e484041d00403000011190007005c6a246440180004c038155241800030070031032581c41c0c0580001e08a03d5041c1000398110900d0114241011420f441d014042205e03115000c4c024009007642c2120321070170713142e001625280e009114500003280c00441c215035900d028000c8500e01c1c8040c02400c1c0564601050b90f00e4030350303200c0104a841d60003590004e50b503441150344924000070b14a10800041d10b4030382141c030346411103951421120303401604454603a230b907060350440104031a80074918464010449007403410b000400e25440204242c2c002070f0384001068a955020040f1030343d200515013040a68032149051000e1a0030222058801c03680540710301c00c56200711442a4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 714931807 1250 714930557 714930569
    0x302060304050f071e05040207030201090b012601020f0403021002070305030a08060415080727060303050406020f03030610140d050c090a080109020306040602130f14090f060a0614090406 82
    0x629003a502e90315160140a81c40340d02404c20075400708840c285250440b17002d4410684002d43d4032916030034140e000d449c103120300500b4a1314130000042c403000615049807850040481d0584c42d4900d0202260a0380a10100105600e800b008100010301d1b2460b1072204c03069550040e240c2081e81c98035064155041200307298080f60351070080181528143c4590450850002d520342da0003810800c01076a80c403101c1c010920580c4140d4101e2404100542500c12038050180c002c4c000251245001070031a046803041d1070152184d440c51900141c80401a68820b070b03400b034480100d002c540d030022101070000500102e480d050400c82810280700c1070280600c10384100a0841d9900303036110a10190661660059040b81d14060744500140d13000b04038540c0154220001588032404203d080520805a6005861040e0300c2440098000490020305190305000c44603002030b81d6603901104d100103c01c80d21907520840c2c0c00b80510001c1d001d00044110104040962418001c6a40100b002c944080e0042 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 714933057 1250 714931807 714931813
    0x611030315040b0307090230090d0e03030706060f0614041d040311012408460b06090f0c030a090c05150403060509150411130c0804330b0a030206030405 67
    0xc0f0000030645284208201400760345410a444d040c2c0a194545d08ac40190f201041304000d0700058690f410010380f15600d4010324200103c47d0740e030007100072001c0315114050119031403140a0384a40d0005c0142c4044a80315028100240300c049114030001200034811028018100020203000809118200000c2d1149034046054a51483e030440304100300c0d40141c0c8594032121003121500094403120b019001d0b06031001e4440080300700d5001d40c2d40c10258225440d04950b00d0300380280820000c145024000940b100c500c19110298200b50780c01007101c0c0344c5580d13142000440c0d00050658000b8039264007076240c003080c060b00e0f800001d49010301c8200407a000e40d8041814010300440d841034036000b0300b0403001800d064071301c80b407048c001003001800a403111041a000e03541a8640380d54241c407400c40316804210004071755001400d0300070141c5050303424004a40282d0000e03054905441104c05000e070300a190144210341880243c00140d20b281d40000c1c180da8000b006884140107075008910400c06 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 714934307 1250 714933057 714933097
    0x50d090b010b0306040501090c02030405010c081b03030f0601090b0909060a17010606080f04050a0201120905100f0f1514042703170c041502010209090703060611030315040b03070902 80
    0x1700000e89006030031594503035280481c03215205d50000200c404a80082c2040c0980300c0c0c00d03051040b91401006030105103002c0c3c400034401661004001184118040092412079440e9400119800c2d0814012050500402c00110455241c02c0342c41c1c2d64491801094402c549481d0410040681801c090111030b982d19000706101490700940c0141d0b0058504074008103510301900d90036600d40030100041d040c01032190b441d440261081c1c010103002500001100d00e004502c05103200104107030113000030b0302460300e410b0700d049002d5070250555420300511140d003028105400c000c042424101c0590388a660751f125100155020703441201a90811100d40c602080c0c90308014080104400300403609610382c2c402c00100d0341070b060946050310780b43e545141c403002400d00140d00a00c2900461580a22603c1c200404241d0641164081d544a0781e250945002418400c554a0005075000c001c0ca40800c60605528101039019140240c3d00804640e4041d5507140503c0c12a8060804030201c5010441 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 714935557 1250 714934307 714934309
    0x109060c08090c0418110118060207242708100b0103150602150601090905040b07020f0c01020a1203020f040b04080d050304020303120703110a0512090616050d090b010b0306 76
    0x854441e01c407106030340a11003480350380740401e040310381035800801c5900c4241c240081b5922641c100211102421041103c0a880328000780d0b40e81d10620500c00d21540c0d480c01c00c004264412064035400d0541d480c1c01703030303803082c046041030320302100c4201c5449020302e000300003030031a4040202044400200d800000d01c18100e100041c240d884840c0c6010103054805402c0007160b500240c044c24102d00e8204480e020b07125040101d4130030615600601e4100c0c201801d0100388a01344203409d00a1180340c081350f09041d00d158881d03480701c180700300d841d01582090103550b0124050050300340607800f46260052030001c444d00209c040e074016270060b599004010070103100344501007029a92221090030054114a0654002036480c1f10390b00100302c0500042011800c40c07402a04400c0390300c041a1a500e40b03500031601700400039005001c050000f00d44d08004100c940c00c01182041c020f41001140011250600500340d61990060440342501d40d5140c000074086151640304501a010f01e400f550b9890410384 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 714936807 1250 714935557 714935563
    0x11d012d0513121214090402030109021b07080d050313060e060403020c060f030103140f1f060e0103080702090702030d15050123270d0c03021f0c140109060c0809 71
    0xe00100301c1c001c0d4040c80c62002c2031344200114101c640074070f01148140e00f4a418801d4a02a062400d90030a00100c00400c501131141c002d0310402c021840c0c5103002c0b2099603001d980e1001c01c6d20456115401c00007428000511540003107a00c40c4a40b1070b400e000808a5072090100d91800e568a039aa0704500107200402d981403240000c500300844103d03040c0145002c000703600f84010b01c4018494444a0000162000180482844401114140c0d02e169942c040c0d614176032030350030b2400d02400f0300d030001c0410844450300f40281a00d4204204c1802d21a0643c240800e00201078140b0f025803009000c0f41440d1000d50242c4001b01c01804280b240f45450403002400e00e500450284e030401400c0c0e0701c41480301c2600400c0d80c680707407000d403400034811a02d034050364a03a09001d04955040f41d80000c002c2d040c00340d9128103000300c0e0302c01c2d40c0003c8581d01050883c0c4100700600d402c000018032005490740030400324452100c400460304000641403140395210801c540700050701c440410b64603810007038614428 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 714938057 1250 714936807 714936809
    0x151504120f0f050a0c08011a0904051f0501050f03120403020411120712140f04060c0e130203150a03120518031c030b0105090a0b0d0209220506011d012d0513 69
    0x54003d0094230040000c0504028aa40c1d10b1030182410340700180901201b0020801e9030951800c482d0369401382140d0401c0038000900485010340c10340300c0c00306038608000510702034000b6449216410681150b0800006d001010f41084500d8010b02003486440c0303d1030106030062013681c0354005004d40d41000c1c43e0580308038030701d0561a180140200101c2d42031500e003844d445503112500040048500d2020b848500007800b0742d42d0042300050f1030300072020700c5030b00840c02070309040c07070880c02c266040c0208008402240001400020054403a180b8240100c02910002c00b2060107400c12100e41008a40b5051360518690184050b5042c40c2c0031040d0107201e0340020080c00c1c40e2540c50000b1110200700d60095034822050500c40c000741c03200e90060540d05071101c245c4000c21044075139404480840200e603841c1512820b003171810300450300c82d6004071082e0060340300713101c020018055441e0041d0351340c41242c12502c12400240d510001410507818809142c1c0196841e141c3d110074800b1036a481e04212 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 714939307 1250 714938057 714938069
    0x415020c010f020c090702030408031305180105010c08030405070306090f0b0f09300f04181505060904060e1e0c0708040b030a020c0a060203151504120f0f050a0c 71
    0x44800b00c440c2c2598040350000b1208002d031780501c1d150b221708200701d1070740c4a0790348158054000400c05040c4540c10880020417a00308951003142e00d0510300c00004480403e101c0d0b180800c031548a0480003500c0c07e0302840d030150041d015a9145a6291142d105842c0d80d40340849042038209003400421110440700ca4100d0850842c4c4109440c1c20540180e880326204580458601e0480080980441420300f80080b450100c100f141c8802d80e819000e40f16401c240074040102c404240020f0040829201d00a00100180102d83c80d0318905030511038607a0100b5003003501305171207890200340d00e0a12110540101d40c2c44201b9812600a0300b58503035169000f8200c212901c03001c20004000c01c00a405030b5050b0f50107000b59607903d443c0c10404000a200798100c400050182c6090b06d0b040c450140d0143d0301c03808104808204640500b81005400c3d50a1291840c070742c00700344800d1204042c2e240700b29042c86d00c128000d800900740c0f41c982c4070b01c114040d40308035900c2c2e00c510310203001c011042d5070400c02000c0c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 714940557 1250 714939307 714939317
    0xc1a0f0612010e1f090c03240218040b040f110d0c05070510020c0a05070312030621080a12020c010606090509040308070305061815100e090105041a060415020c01 71
    0x20500003065210b008004201240391681000c1200d44c01d40c5030702194a141e404000310a0482d5685030140b10700d507580300408021000581075210005050003107034502c680803c0038003010f40314001004010403d00380c10f180c000d5614125441c00051521601c01c55002900714152030340d6012060b00e0a550200101d002004414011500000c50001351903101c0400490003607181d1034600100381c40d103e4042c0c8003904034801e030400041405101c1d92004440c0704540d03410311800f40c60b692003a82d9030ba1100d1214120480c905120004070b184c04002e00103044d1236140030201120440c5011080c1c1e00060a011980d035940c490410030103800442202c004c02d01501c0076606442d10340c07009003141d003009001030240350301caa0010b034107940e844103d0400160005440710041c00c104444245008c0741c100010301030800607000c288664000c00907081c80440081184520f40c0c00c01080c0405491000b91107000c00075030340740ca080b041e642c800140002c1c1113140b001c60486000c00038000e14101784140d0745410301c8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 714941807 1250 714940557 714940571
    0x1020a030617070f0909060209061b0118030203120a11070501020d060e010b071707150905070803090a031707060e100b040b090a18080408011e05160c1a0f061201 71
    0x90490050f6608440e848400000c41b26a6400d24034080c1c46262802580300c0c0300010080011038106500404560544008001d00744d0721492035030a0540d152000f80140e8010f00000c4207030380c403421445501c130386086000724031802e0320000e101307507500040821202a5000314803107560710301a00c0ba8100400321501481c0f000c1d498403030300303864034458608041c1c0a02c407420f1030002a0751031102200c5229070b1095401d00303d020070b200500028402200c4c00c4a03280070380040090103070030000a540b410340004081c0c424207843c582d103003140621030703642140c81c860040c400c86010500902c0341c0f60981d41080c01510751484182010412160324503810340c0b0031850440028003a8607402c61455111a42c2c3e640022450b910030303241d100341647c1810080240c0c0000501041801d41900f081b200010720031700c1c1143c0c0300307403c019071002c0d110708440c031000f0410600c010b8a0114800c1c080381d0203070f5010f51030100c501d000c1c0001c5500340160448070381402071681c10038004142403208880d60b5204602d0000c011072 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 714943057 1250 714941807 714941819
    0x11715390a05071106120411030c0303030a0c140706050108281520130e040209040b0709121b08030909150109050d05010b12062a0c01020a03061707 65
    0x180224842a01000000b0456104106100c0302e40054094010003061321807410760b1600b06c10681c222021a041c1250f54212085030a001805060031803000b03000e0360440c1d4514600340010a00a4484010032003d100b1420b17810501100801041c2e02804010400c1e40c100428145404858200040340010440c403c2108001040382080096030000c01d40c1d80b9807096400c01400b0303054800c8041070080c1c200c220a2403840c0e0070750040c01c91040e00c440b012403442e40c440803440d248104560107504884602d00140000c0d00310307100c0550050300c0d030400d00b036000c5d00da01c880c840302103646500f125030407200311500309c040401b400d03003000502d00000110302d81203070f0402040382c0c1d09020f421100e20050803511413015030301480080c4040e15028041c000503144d01c1c100a40607051070042c4c2805020380c2c0480d891062801b00780e10707114445d030005d4102c2444022020031203100207001c03102c1c4080310520130141c210300b0a000400c0c0c442640d41d00800c0141c10220501c0803107040c80084000740e80118401c10030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 714944307 1250 714943057 714943171
    0x7053d05030c13051f020c031605090604060b07140c10020d0e01090b0a0c12051204140a080c0f070b03100e090a05030f04060305100608011715 63
    0x4442c0ca41509151560511442c54125840341d0700301650114540c10840e010082c100d406803160380250742211808807812080c50b4440d0820302d10208a08030130801401541001d0420035007043e00a03200268080c1d07140200a40d070382024408841004581e490080381303840c00c1000108103001161002d20050308640c021350703070f507660745501c0c81841402803800c05640c1c011101d0394001e0043c600b405959040352071004000c812418401c581101504445103601840380041d00c01c032500c03c038460310081c0ca4a8941e0028a00c0031b61800030701c2d220310442000010421409051400c141d0801840d17400d0f1100303072036030412126400102c941c05081c4200403138200c1000c0800d08031900901c00c1195501d82c0312840d414440310540240c0345210004a00440c0000c400c014012a883e50b5070800241c3c48180b41d04400e02c02510a00001a240c0b80060010a04829540c0d0100f0708440841d0758080b99034040b881004002c440802440c202f09401c2c551200340b4007145020310b15110700b401d42d01c0c0d11503085152 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 714945557 1250 714944307 714944311
    0x105010b030f19090506010b04030c0801020403030e12010603020d0c05010e0f130b01050c1615030c021f020d0c0f020c030304030b2206180c06020a02031e07053d0503 73
    0x5503d40098084140c0c031001a0b108041c0960090242c441560f180c0b03d0181c00360f800391100b1182c1d10701d141d00014017000e061095406036503142d641d00707404c9200e039001c011421012801d03044240d542e5070750001c016618601c444200d244200c850141561a00002420441010842601442041c6500e4825a403200c10a050007c1041d4001403100c0d18171004031082d000302e414019103449070344101401050b0725240b043c200d90a244001d480720072040780803815201c0510407034025a01040b604520100290034410014243c0c110060402542c0c903031080642c0c000c0100c1d0b001246008241c2065a03606000310032a40e60240c1c021480c0c00e00d95a9000e05c8554010a19642c02803001070350b18140c414140000700003074004000748483c00000f0380c48840d0200b0310074200e4500b030040b0300000e4010b0020a1034880340e40c004018080d10300c03048007a0016004210004ca017607001e1142e0204841e5288090044810107080e080a0300e012410b032185e4110a95070303140607111003140f034854680c1e540710040325 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 714946807 1250 714945557 714945571
    0x80a020325051e0301050f100801030b131e120504030b01030206160b0916050409031e0908240a1107030f0201020403060c1e090501020a02120a0503030c0c0105010b030f 74
    0x4042152488012202d90040f2a56800c1044100c0110400840c21a0155058450807581111182e048a003082103a5441181c2c860100d5250001080843c01d200c2005074402a001c40303407201d50b0100e81e580d4402e03e440d46000c21590304d20207006814800e0300d603010443c00c565414a9441d1a0a40c2c84480040c941403000a00c01c4000052030035203410603100c0c40781440e62143c050328050802411440d180c628408510b9995044180002114902801402210364160704d8076a140020100b800d10303604003441510007440a2440f00040d1000700300001950711141d0950124440380c1066030a9041002034113612100f400c062b003142c40103440300c04070346c6499410304080c001d00b80f41a1040c1d02a000329440036164510f4240b61a04036a00110041e282c0b490000661001c0c00d81190107131400c640c1c0e0b02400340103900030384000005090800d03130085090f1103081120045016540c0c5c2c1c03072642d03108552004d074905011176a0f035001c0c0b1090045a0150165030205800d6140c10104042d03080001008a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 714948057 1250 714946807 714946861
    0x3140f091c060203090a1202032a0a14010c0305060d0209190908070c03050c0409030e150c1e1203060d06020d0905070e060127090e030c010c020c01080a0203 69
    0x428070242100001144158061415501c0b071820078046911504a0310041d243c10039007102c9204d03014408001c540080061a84d044401c404140220901490a803001140e502c2184101004506000040000c10403490300202d00100110b600605a80740a01003500070450146100700594485141035489546811092242c16403d004d40d405482140d0028050b0900064001d09000440c403e07a42920301460464014187c801305100403554039000250005900252588091074144c2044946030004440306042414440400307081104400741c0d04021405003003101490181840703580f040d032740c03010540340c15403810b200404d00403124105e004100319030004070022803d03ca81d00014085410204603100151144c00c00e1000e058241d0302c07a4042044011116000f10044000c420901e003142c0541b0340c076a1400c80c1c0140a070a0041c0807881c0c0d030109002071807150609208901000030940e00038050900303a940090480d25024026403075082c0100204105000c9050f40e810150609a40d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 714949307 1250 714948057 714948079
    0x10c17011214160303020d1b0c05150f04080106050f0d03051207140307020c040f200c0c1804021302030720010209030706090e100602060712090b09010903140f09 71
    0xb241e06159102043e149110761640e00801855800191180c400015849034403900d001c100743e0100340c1c003404500074400044800c092190f806c000706c0d80d2248050090f281030912025511848058005402040c5a6992028108020704c4c00f00400544804140d84031100c1c0318068070024060311800c0e0b002603810740180702050b8050312070301494017014441ca10710b5413a03090550000f9214058990410700c16070030701d00340086140c000d00c42c450310698040c0302410505145110040c480c1c01c48040f50a80340610020303103c03036868131603500d0005134040340c030903001d03107458410020002e400d2000d80641900c148200080c10760000304041e03130b04141c2008502c50020001c002c070702a00c03a116090742c0602800000150181d0004650000d90703c003a010b50a5554940820700c080c0c850521404d00103912005c0807a040c01e00401c42440ca03404405001f0038010010f40f01d02d554000250f070404480da6655070520f0034180d101000c0d0000003489522980390203440c181030042c9000e5081028400d0b248890 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 714950557 1250 714949307 714949343
    0x120c0405010b070b31030e030105010f0807050d0c0504060e042a061107031509060b06090604030318081e0f06091e070509070918050c0d09080714010c170112 69
    0xa041000380083c1840c051481e50741b89002803000c0194940c01d400ba600340300005c103890321800c1141042e1000000100041890942000850031591009a6140014080203e826120b074050784002c0c0030709064100305400c041c44c105081181d100c40400c104400a10140d81c1c1100c00041c4408840491070700a103140c00702584281403040540c030082c0a20071494165407880c20503007000070f1413402184d0403c40b1582c520140b0201d4820100580d0780100100811310000b80100d13001702030702c5e07a502481c1c0340c45504e50040c00e107401c04039150010b0318081c0b905828030560342004654560341c1c0500190141e4100074007010303919403081e0714800001d540700c0c10494812004015030343c024203000b0700158907802c01c210050650b071124000c80600329216007484c003442d030440c05a103008a01e02a4103500d8251038886101c01092020303002c40341100200123450106645248120000c0440000083e00d615060000f070302010301c50020380e000400c18001004004040e44050444903040b032560b01d0b500c01429 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 714951807 1250 714950557 714950611
    0x4240503150f0325181a01110a060501080304030606050301180605150a1706010602030a020d181203201f051806010e09070e0423010b120c0405010b070b 67
    0x981100c075505402138003498401451070740c801c22100301281002c0815001c80c0720b402a9050b4880340c0b032242c80c40e074841c40381d65480350500142d9042442d00351014400b81d0b5646000340e0300282d0205500d64004070301842400b800344600c0340104002c0380200103042a0100e07036075121a0f010340241049039108001141c543c104101711851180c01407505220940300c01c4201c10b000680700c2d0004480c0300350b800116000e030000084031f9503103074030b50000d0500050121044441d4403008640e0046050304070b9000810718002c0b40b41c04031044c42500d4541440700da000044441c1075034412a01c40d03550003400404408500c044808400d08a0201c0200d21982c51400c0c5415800c500801203000d0b104100001035444002c80080c2d0103141d900041c0d900c0c0c02d65800c4400d40758082910060a0841201c04038072982019500c443c1c1c105a401e4004651040842c000880d50264605040b809800250b1030541c0c51402d48106400741507081d900d54200a8280c039541030340180248051901229826014482040a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 714953057 1250 714951807 714951823
    0x60518060f040e1c020601032103090b013c03021908032205090606091908011e1b1403040303090f0606060305070c0b0a020d020d0204240503150f03 65
    0x18005000c2040141c03c019030384c500c0c00301d41d200f0400c181014040c02c41d00c0494124100da400010941040014200588407143c0710f03000c0500b4155110070304c80c0000d0034502c440d80240600030b6903031103400f042076488480c12460501a00c01f43d12044003c140b400006821805894040e55a040640703c00017803400700c000d007500110201e1102084200d00740d202c1c1002d100c02d80020b20300002015545070140040c658050300c000b076005070140100c01803070820041e40700c01d100801e0025000180d44d1010b881c21030b07080c020440041658061441d1101507c1d0180c000c42d2a400b072b0789441c86040060000b40341100341e121030881d103200000814180342c860741041c41e0182c0c00041e903a404905910b015401845140b0403000841d0030040040c007154018104100080d4000c45059001d07600e091012000398000240c0b070600c26030074000302000b49014405000a408a1030f103030a0549400c1c43d9030040741c02c02c0441c1d10100b110420801c420500b50656001d01c850050b205032090100800003e403c2c0b50070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 714954307 1250 714953057 714953059
    0x21c210b0603091e0a0b0109020309010f0e100e150c070c030c0909020f18040803060a0f030f0c08031306080606071b0e01090902030304031e050703050303100603060518060f 76
    0x102c28041082c0021500f00c00a0003494104941c1c4140d0b0329a0540740e806481001c1e00c1000381c000101b20300c0034981c000f5544011271300d0001038a0128005010225104081e0080c0d0aa001300b0b900002d8031101c0c0318040300498034000621002c100c2541c1d42c034040c81d00924484d0168004206401001002c0920101655114401000035512246080c00403ca0880709a01c520101103015185040103500d21215170300045900a0b0b9540c3d5440e2440246c1c07010302400d4100120a100107408038013550908003443c07103188148000b0102c2c0c185080c0840554015070101e80007000264800743c0140510701c1141c070541490041e44d80c0340c8000400714022200c01070f08100041c120520114258901642600d00b80c111008081c0d8844450764212900480025016802008180046401228803500924810250310407200107a5a0b1070306120f511340c41110310743e0020040c0310030303444000b6005000e0000c5103002c0103014903150004e25904504100d5001c80d0022030041882030303c601f18a6002c1e958 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 714955557 1250 714954307 714954319
    0x181e11060c1518101a120f012301050a0e0718090216060515010c0803090c10091409040f060213050402191704021807050c06070e01021c210b 62
    0x601600a0407806081e00350900aa0140c001032082c4c04000d4800c0501c03054101201440c19002c420a01910303010000e1803440b50301c80d48680b413040c1e6009015501288000350030003900e00002d08104070600344103070042032040345131000600c803980c40c404403554044860f04d0000a00103d0b0380e01e52800c0c1a0541140880038000580b0390a40c0703150011080b52684208010000d0356a02070340c055034001c101c02c8481c00a10460000c0c000705180c131000c3c40d04049000103030f8003031400e103000040c003d5034100c0c1050702103406020208103408401c41c440c020080d05440c448854a010768501003040320560000700200d0340459480e6003070b100400400060300015008650341e0150b60000101c485640509030001488140d4070030b0006a403d4171140215805008404010701c0c00e40d60082d965001003030b080400105100300b1604d51001c1002600448568071504c2207054000002802c040c88089221600089484800c10346580041daa444a1a0203800405002548200340d00a0400050241d601c04 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 714956807 1250 714955557 714955561
    0x609220c141003050c0a120e03070c08060f0705091e10020f100905030d021e030a0c0e01080630150603011b0c0803040201030609181e11060c15 63
    0xc1055100400d401c0011128002c01808030386049065031400ca424180000c42842500c03044c83c003a00194052401010011a451404a00b05403654003d51402c0d07440a00305101040190000d010751500300d0445030408945240c8040b0290541c89001346407401000a8a40c112941c100f00038400054000204005814040000002d40d40e1007400444c801c02c0c010300d003122007601c21a225451406034070101031800d02c08400c1090009420081c14401e680c070100c041c01d100022114011b500c11140a5000140e4202c1d10740018154811485802d06200b07100c810700106e503550103d01c41c607500452101000341c1007440c0d07012552400300303070200059120b8021242114000c07235007450f1061400354001c121a11a41c291550020403210b0b4000c08289180c0306400440e10100007540c0c0207006040108400381c4c1c508000c001c580440c1b041803190b820719079003401000007422a64918001e8424088046a8076403110b2140101d99288030b44102e200143c1c809901c2c0044c440b801c102e03800e40362030301018 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 714958057 1250 714956807 714956819
    0x8032a030c1b0a2c01150804150213060f1d090a0f0f0c020f0f070f03030f0c0f03050901080711030d050a1d0706080601031e18080406021506090609220c 67
    0x15400a0001c84134010180c0004507090182210420b407405046d5242040303602c590300d400031f040d0028038580748855020401a405008061450002413800355103601c1d03105030014006021401b00c3c45200c2103121054400e0304d0302d94502c100e03d038125240c40400101040c0000520000b00b10705140e011619041c1a0318003411034003c6200c000c1416940d05a03207260030050407aa403600440d029224129407030b81e0003440071911a2585038800e01c1a42010708144035a600d0b4100220154081100003c0c00041c8400c3c036035074000945608003410f0706212600c203055264280c0c41c1d00540309814910b41d51103000496050b0b013600034204403820b03041611515125910b41940b40d8101d03005400110303800202141c4c3c40c1d4444d1183c1c100310600e11040140711050806800060603c2c3c1c1400552040326421500100e107440b0002d10042c0786e83d80080c113240051017903402135410000c04040c840c480c0c0c0410004651662034085034007041c41081440b089820520808100390710502c094034041c1040d50110740 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 714959307 1250 714958057 714958109
    0x6060e1201061e090e0f0a0f060e060117010b030703030504061107350a050604021e1504090e0c0307030b0c0c0f010b1302031e06010908032a030c1b0a 66
    0x2920800341c400d205207001112244c0d0340300046d503032800c6941c1c00590030b080458584070000941d50300c18440480c4420340701910b0f925050087c0c0141905c21025a03070100c030140c00b4452500c00c108181c01070704059283d03481c007902d20f010f01d10460b02400b410181869a821040c0055405440e100d4110604e40c210420f210103d6401b0520001604480366030700c80342e20b00001046450a40c1c00385c020503103030359146d00707121001c50a400100320031035134036002e00860f980344079441d00c40f000d20b0400141c6440c03905080c039080d500c18507994041d0f50442d80f0851020b46002c103400341900e400681e035990f55144d01e501d034a400d200b1808058600e00842c1c03101481039406400107103c07005c080350403040c42036424204804034841a514518000c0c2d403210304012049505151540c408814105055065541c00b1b0450940d404400c406083c800000f40c0b900c08840054501480030122030019410481c04001003136946125035140003810300101c0400110382d854403040d00242151404100d485162100c600003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 714960557 1250 714959307 714959309
    0x804150f09060e060f1014040f050702011a0a0b0706051003170c0d1106060f0126060a1509140f13051e100e19050c0301030b01060306060e1201061e 65
    0x8858042d402c041140d8005440c1c10301e004c2c1ca0803a00212030b0358501780030307505041c40e032458188d000358558441100c100c101e8401d2a10a1310070780c001040c880c00c400d5021031044c03141545a03201d03040019040c0629440341c01500c0340c0d1135108500042039240d00150a081d841141d1004002c01c204088104c261156100541030041e01a030071610f05201000d0241c0d0400f120004010042c1e22080c0040c03c0c070714000396100c00c42e41060412202e2004d0700f0610002d010002040c01010402600a00c00c040c02c050b01c00c038000300003401000410311201074004002c5092841a8006071201b2520500c880c3e807403d5071011503800062200440080d581c02c0c6101a000841c0d00e103a460400d001585941c00414071010300c100c89401d03000104a0902c100b03480561000f800000f00d000171203110340c1480c002d0b8402c43d4020200740e040c0903101e6166181003000442c058000508042c04c3c640c0801c07081d41c115171805086401203a00035401d215440e00c0c503004203120392141680c0800800110b00071002400400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 714961807 1250 714960557 714960581
    0x603051218060405130b040b1e0f0906010206040308041103060103030e0415060e01121107080c060a2304050f100b01030c090302030c12030d09060b010e010f0804150f0906 75
    0x1031691181042048018002c512820f5000206054244c0c3d03407492071b60200d48400c000520000c0d1070b140400204401c0012000d61034955151060031100f02d240c011840803c0800c11650420180781010000f52a034070301a10080a01240c0000320b03040080c034129004120f4006421920f0715a924100282020400313204140178074a04010010100344452466050711155160100144c001c2801102c40241d5880e500e41c000d41c0e105105174200e00c503035009250290240410b140c5450b00b06002c2e03810312a01034900603035617181c0054084000d0321440001d082100c40a100749407a91103041050a00c2d400c0b04880d42c482c000c803000c40e10206034580c861049040280d0341080464071405040c3d642204600029605620400303c1c1100c500d000e0349480443e510110589040c03041c0c501662007075a00707407a8111769950315003c980426581c0030664a40300c820919023101b402d40d1088001c0d103011805072026101c012100406059410f80d030308894206415002e04019101c1c2a050500080c0a010450 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 714963057 1250 714961807 714961837
    0x10b03010b180727031101050306090711030c01020c0a031b0b0105010e04020c0f01270503180d12020a150209090f06010917031e042607031509050606030d0509010c0606030512 77
    0x441c3d11f501c0368094910403000a0b152200546401030107444589025059201600c410000064900e2003800540400c1e10749400809518400d0702e0041c2c0041c20083e85102007484120050011a080440460440308207081000c1950000000b00e4041d11920744034000034402c0214040c440d00c070561101440c0040c401c0414100e1032142e50b1034400d8140c040e40942964424890414000c44001a5041001c002002c5100320b50540e076603081c0c07814803520f05001680060700e01300c0520100c1d40c81090540080e01e000c5240c58000000641070100c0a455003101940f0700d030010360903900a020000107010100300000c1d118003403401040e96030303201841c10000b04200d59800240c880c50750007554182c2d60300070740845c07122559040c243c200c101c10141c40c0e4181e00c83d4950000201d41c4040303420080b0380001c5e0000c540306905050503880e03e035014160303034025849101e44519640c2c0c800191031120800346010b000281d0503081c00ea000c0c1046420203030240c02002041c80001003c14010302c4100a03419503 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 714964307 1250 714963057 714963083
    0xb0601050a09060e06160317090703020d060c171003060b0907080f0702010609050a020c011406060306060d090506090a1b0303080a0c050d0608030c010b03010b18072703 74
    0x110340300c0c091010040701041d4006402e0095034010102403070383d000082c007210f083c40c4042c1d078506400000602e041d00859608122090205541c2d40300399405160300009290707051550740441d0891042c150050241d0740e41d10626540c00b4482c1c04a446550210265102141840d0341005c282101074401251a0381c9020260001c5040034130a00d44951b0903903c88000a54030f021b8508008600108100115541c41001043c941010321a1900451f00d240c5c0040c4c0300c03800c68000c5400c68a81c824401413202c0365004004465451404882d071003101542c0041d01c4013a48010740c000b40040b01c1c1d0040c00c9015030070421046003c00925213421740d000b4003c03c6205100500101040c0c0d00c0c2d8040500010f1030300000408402d401d800c02100ba005c40e203001d6142406848404049410b030340c03c86041c5400004111003810400d00030313814000c2c8100c00030421911024001003a101459052003892840c003000a5840c600131854046104041001e01c80284114580000180140d000c00c8480444200c0f03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 714965557 1250 714964307 714964309
    0x80106170a0605130515010e0601300608120306090f040c060516230f070b071e08120103060f0e0c012a080304150207020117220506040b06 61
    0x440340440c0c9400328060034040c0324039219040644070051158482c104a1000c2800060080144640002c1c50804c00c1a0380d504000141003840000b5103424104501c1d1501c0c2201030382d4111040d05500d402c1c2401d0701000200c40101c102030b00035544020320a00510032003146800240004511482d01240e2508466a864a000302c13091801c0d5070140c44405091b000f48a07950054000300030030007050203810308229850b074811080d185d000901869003000713112034014483e41000700502100e06840507181c0b113401c1a2401d15607016a0002034100101c680f40300b4050a040e40301741c21313002d030012242555070545902014003907a080c4011160140380990b009407111807440350140404414001c1c0c0800c03c207440c011150202c0d40d00702212807842d0404d0355100503a03800071082880f032060214684070700d003074100080c0c0c42d84000c401a006500400050f40143e0307103c3d85140c0e641b00351078522200398403100e334030140043c020025000ba44504071042d4003809400145144241c2c440d40012005940300c0d4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 714966807 1250 714965557 714965579
    0x2031c020703021222031a0603010203091506190b0307090e0c2d0c010c080619060f110d030e010c03090209060f01033e0f1b0f070f080106 61
    0x1c0030140068110680301a00c0e900c075200180107840018051014800c40002d03501c0c41460103138400c5031403035440724229880d844400540d07544550b044000b1811454005030440d100c2c000315900711132244503034000890a9031100403a0260080c8003080070076158627070122040c590320940d00000405c01c49800000e4094041d10800c0c81040000496400d000e8880740c2d80821044800c0c0400402400300999580c0c040e40b40c018040100e0740348004158007040030f00180070340c40e0182107540034800c0100120380c00003080e1480000c48549141c20061003150103012500038505500e21031311030003940843c16405034103401c0710240c014030f68000c01501c00300444c00da08503032035004001d401c2320b03c502c00a503040c904034480c48a07031b0340d060401060610800349441441e2a010b00c480e84c03111000540c410074411188030030020718203641d46e1140f408021512001c0035025602c5a503003c003002c441a0303c819030090019086451908013100c1045850f1400d044503031082d805284c41c0c40d8a80440050300302010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 714968057 1250 714966807 714966817
    0x60d2310090303230c0f0708092d030f06013f120e01020c120102040e01030b010f06080c25020d05150a0902011e090f0306020901080c0f181f02031c02 66
    0x258445614001b031682c2800d04035001080190380300710042c007055030f06481d03000040c404c45e01d052402d01210725800100c5001d080094516900a501240300d2000640c000181c06056500c0240c0f0050304031100c2c40944400c2600d203d450f9007040b446848150000081d10034581070510030f00381520308001c01ca90803104240069003850041c0e01004c089a403505000c40440314028078040058031301900e8508400c0c0c01d80c1c0c01c0e8070844440c50400010003850850203c0800500000c1c079040303400307082c01d40d4240a00e00410480b20001003d030107010070060894003c0c0741701c0a5014040d1004805c00c0e0034526181c40700d881a10808001d514002804002c0c544130b401003d076416180c92240700e0743c0400c5860400c021054078800e000c01c034030020401040d5601e118004520480340565168815030004000d00c030050700344117075504144510356203201c6c3c1006442074140e040c84c0c82810641c2c81000203941c030300d180603050076000b41404100c2da110750120051560190b00c5190029074a6400300c0341d41203202d1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 714969307 1250 714968057 714968071
    0x913050f040f0c08070f05240f0c16091401060306050d0b0a24170706090509040302011e0b0901080706050a11070504061805060d231009030323 63
    0xc0090002490750125120680c054820780b4420b80d103c00600c3e10302100394100800501c1507400421107403400b0f0b010001c01c1c4480b0796602c02581d10b110051841c034043c00750079140d01480442c5402810320f04004452410f11100c40d01e01495039240300040042688010700300c95125030b0340003c02c0c0f8034060701034141100c1001e004980400c1d201e403601c48101c1000390101c1c1446031901320904104c0681c00003044c000c50001001d041e458602414490064084e41240e901c541102c4800c00c02030707821103258800c8a5013030350110034581c0e503407508a0050468481541814841260b405040301455001c11040403060b9103580290341c9858920f66125214401d440014204020fa0101c0e94411300c81d49030210131074011190465103500c0082c054070610f0b04074026032003a0b000c0700074602c0558060300e90412340c00e455503015030510303443e030380003030031041035140084c0340c00f1b15162208030020008240381800d0038404001c1c120700c51030002c0207401c41e00028444c00b41011721030440301d12080314060107520 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 714970557 1250 714969307 714969331
    0x15010603020703031a2209200109170c150c01140a0b030f0d180f0e070e010516031d15070c051012050c070609031101050109090b1b1608091305 63
    0x32000d018160100f40480000c1446c1d44412104000400c2c055003030300d40424441d02c0100d0304000c60001841c4600550141e20040c0c043c419000d4080004201c0e0041402c06440d04101c0c03c0a020302024144900f020b41c4150f90300c3d00403481e10300c6042c01301090084840c08402e00410003450101075451504a404141c26000b03503485007070709409581e442180e03100c28099404c500c0e5854041e142d004200c0d40c0159203044000c000c11007465031019951003600000d0030300505049946800c0203600100b10801400d02001c01e0001c010900c1d140f507400449803004020440ea4141d40281c0417294000c2042140c00265081001ca41807130601500c8000001da1754501840510400d4244041e00e0041c000302d0100800700800004200c1c1401668010750003511030710400038948080600b103841c168480c09a2074030f800001000a401c1c015215001503204549010000700072030203511a2103812034034030302c100c40d80415108100d8000f01030142104111680c4841c80301182e03c12040d18011180b81980c98 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 714971807 1250 714970557 714970579
    0x9260c1801050d020a120b06090a1406040504080f180415050d080901030207140d2a0602090316120506150d03031d06010603140c040303020601120515010603020703031a 74
    0xf0600400b00800c1c9400200103401482e5550b090140b08140c1072001c0c0d83d94503200c000c0000508201c030390070303810100c3c001003000704409414411b03c1d00f0300301400307080c4250f80720740c041000e0041d40419a81d40c8500034a0440e60381070131041c0c0b20f1588a643e5042c9008901b0280b0803100310302900e07800821101d0182c403460040c1c0669036a15100ea0040a429047c190700f03000807408103014500c142030707042030301d40207190500f1361820250200100785001c1c0040c2c4606001040b0401d104c12a900846500450250326800500002030030000a0011521483c0e07512000003103600e5256021003005001d40203a80307464980e1085070891039944544160449401400302000138840e134081e80c0040302e61f14454020400c1c503140305003000d1080e405000040d07101c042000d41d0741c1c80c0075046900072141d141c01c603207400c0c42c5940c007030746645e014031484007015000e080201c14041c080c00494070000101e1a01c410b5903071a00000743c002d400030308003500080c2c1b500122010340089203024170114000140104611 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 714973057 1250 714971807 714971809
    0x170a0203090727181a010510050a0e0d06090b0c190e01020c0406291c0509030408070e0f0603160b030c09030307050d021c09060f09260c180105 63
    0x80c1c03d4010043c141d40b8002000040184680010802c9030411450340300030300d041090b103008400c5c51001003a468103004012582d40e1031800c050070030840c240603890b00d2401174217881f841c1c0403424140e00060800d14600070070440f5400705e0b1405110b50841c144548031130040380031900600d051222034555903030050b88103500500c240c4030300250510446955140460225081c1c80f180e90120560046284c0c0300c4000030181c103415019013003140b08045c1450b04800804800c07800060302014201c0d03035a0701203401c0307400500c1146d000d425004101c600c42a903502580324001400c44111104040d0003001c10281e107000724101c3c41e01c50301104558101030600d02aa600343c0e2001e003955481d00001c100c1c444083e1410310141c400c1130f000e480540410600400e000c0e08104518207503042d00c400c00300248842c0b41c0c100766034201740d44161501282200c238032942622051580e8200000700b8810b81c2c8050100c1c03400c840b140c14031400e82c1c81610194011381c418014825290003402600c41c032620b00621a03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 714974307 1250 714973057 714973079
    0x22406010c110d060b030d030207080301050f12060c07020a0522052a04050307050d05031b01092a0e1522050906011e032f030d170a02030907 62
    0x200ca40104010502c010860300002c2d203603000e41200f16241a100e41444149240c01c1c080c801d51176003581019031620440342d6980f0802c4c0b105026142c440e914404080c80c2c207840d00681d4161800300d040803105c540c181a044044175030481e5000701e225050b1000702046070b00304215003012003004136514036440c140d44bc1c0d010020f020018481c610303490070044807500c60307461440b140300d00c4440a401c03180d4460a190916042c40300300d8100c41c1c058102d491441c8001340c400000c44034580c0306440d01d400d01e07100500c0350f07038003505600700d001d002000d80d00031442441e016808102ea114000110b80c41d01103a84580b40640004100c80c0c4004880480b10f52204504000c0140000201c12714003441e184640030226104039501698504825802000103004010016400c2c84d080c0c00544001c1940724903598412070106407041040e9034002003521590020000c00d0300b114000c940040a841d980700135a00010104a91b4800c419a800d414101141074410140b003124050790142c0061f00f88641071444a8074 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 714975557 1250 714974307 714974327
    0x8070c0f1209090509070815130606030b01170604021c0c030605100501090b070b010605371805030601120212030c011a061603080a06050405040b060102240601 70
    0x14260189000c9a4006600c000c85100d00c14440e880e0b00c0b0205040481080031200010500c0e440360b44180c10504c1800000201e040303000c10106a03030712843e9500d42d59040d0100c550380f801048681000d20200420426507100b5040c0c400300c01001000c41701c80c03402103a93b0281643c002e50483d21844103504a03004401c0e504001501903049418070aa4960b00c0c102151b0040759503020094070440180980e40c3d10500010003040741094083c1090320a4551810104c010b106e10401d1040000310f441340c003007c80c14100800d41354200640c4e00c0259450310301c10f40030061060140010480c40d0740e981300441103402e140c107440d0040c1c0100341f0f5a09207213234036904000c400d10999002440c0700c0d1541000707000308001c1c01c541200ea00041074084814840c035481d417004143e0288100340c20b02110244ad12903400048401da0035107460b00151300c41911800041c0419000903070014107020030001031050300351307000e070003503200786d00315114110354001e011820365416082000e020035400104400c2c0d0702c03942d03190f0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 714976807 1250 714975557 714975563
    0x50702062701090b0a02030601020706020319050d0f0e010f0f15140d0c091b0c0b0a0c2307210903121803052d07091802030a030503091c08070c 63
    0xa03c0b001a901c0b8880d50b40011120190f4198000040001e1940e0500a800c02092580011420f05207460000d0301d840c481c4161650800c900441c4103034013500703a03422820400e10724a004101c40060f0340d03015406030403009001414182002d00d00300351248030f44601401899140481503019050181c41c800c960400001541c0c0450901c088070080380c42487c400d001400007020010b5104080c1000c40c6100e4510b031002010b02003d4141a0007040c0103260490348071390580b800040c500c0c426042a1180080102034210b46c281400c07402ca16005590010010380d801441050303141c4540c070b14030411142d42d2440c12030006100c901d08100080b010080d00044000e01c4c2401d00c50007800441401c2422455402a81c40d075001050540d045500c400044455808803502c0080340000700040390b6442d19148664400f2a580d61104e0780b101e0f0600e851081c1481e802401c1c0d840428940c03c0042283d081510012068060610001b100044100d01d455044100d80c50301007003640c031008103685c07603840b00d0310030303 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 714978057 1250 714976807 714976811
    0x30914101506050d0207051e0609010e0303040b130302160902090109080313050d0807060513030f020d020d0c030c060c080103031209050c090c090d05060a15050303040504020a050f1309050702062701 87
    0x1119203e001c4504034401c1e00d2314407000780140d141c21790780325094030882d040e040e903550004c009200110300310402840c0c1c0300040e444969800030040c50100c0c41c1c584020044040c040c006100400c00a640d50000e1003c0b040c2607988031021625800c085817a4480c0400107024003030051010003450400d0702c1c03840080c9001c0c00c0700030f003440341e20f4a59005440e4111400312707400c400ba940000805400c443d500c0204070661004007081003190714080e6807046007110200c14030070911b800104142c4548103015480354010b0040c0080810150064140702d802e010460205942a0080c0c2c0b0170581c6105e85400c0d940c1050040007030751000740521040b0f580c042c10800e40e80d06c0400c00111b03691504102c401860307104000400c098644038254100700c82008206006485081c00c04120603580002a0340039110304403801aa00d0b075003508180c940780b08051401c0c0c20740d0000b00341c0f01546001007001d102103134880d25040c045c65440c15400c0b610790f07408490b030360020801c489540c00310607102d1450740800f000142c00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 714979307 1250 714978057 714978073
    0x105181308040f050a09090b0c0903030d09060b0109080d0206011211100207030605090a0221070e010611070b090303220803070605040516060c030f030914101506050d020705 76
    0x107101c4103503006800030381c03002000351010441804c001510b440148a80e803002c020031411541c900c045000003a001304030425000c03941440c0360394184111210407105040400c02c600b441e107440000351070241d856074046014802e0001d045100491145003500055004e07210780da080202941c1e0400304d122081c0d0f15055101d260b10a280c50700075090582c48582c2d0001d200a03891460250b09450780285100d02c0360300900f408600523203d11036180da5034442a6030b01402c0790481c0504a1601c070169121415016280340001409508100e4070004134407502c1c29a940c680d220a0428a907203d0b010b0300c0c43d05071384100f0000030842c2810030003128001300c180d014a0300e01d0341c9078285890b507000305c002603584540d01d034148010003004120002d009030200b0244c2c01c40900e8510040d212803503698018007800905c1c9201d00846200e40d100c4012194000f54500d49404007411060b941e2802d0410480b034245081d44170364500680d0801d07035081f00c3c80f6640c3c90345011011903610010f9005000308540d24031035608 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 714980557 1250 714979307 714979313
    0xf0e060301260f0c04050a0b030d0c0b240f040e01050106050a0e0a050307210f140c030606030303061318030f02190218270601050f0901051813 63
    0x314000c080b101c451148103a1030308040c40300c45801030508503603030b4410384030300724000c8011030b840302060811100054580c2d180c80381e5030041d00e110488164140a603040c3d1901e1540c03c071050384031307203405030b04544002da41d09101c480c03014042d80030140c07000f11f419201e0207062422104415207400050004154600030719041f500b950400e81096011030000301d410310009600c2100c8108002d0100e554080b030b40c0c5410003080d1146050b0007a20716018011110204003040c41d0845020340754000200e09170045c2904081c405442800e100940c0c6004032030900c1d02600e00003400c207014020050145155440381002c200e03c0071203001020520700d0720303503282480c0e030000311486083c4140a41c5a001e4182c000207402801d0200345401c2101c0089040a50b20158030391082c1d100d894210403c2142c0c4649851400b01001c0f241506c4603021030300c3c40810300d5080f80c1d010031046c0c120740c4c0c151810381c040c08101c0b00b001404402401200d41044208000004000745540f02e290824100d8241c5440030320961 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 714981807 1250 714980557 714980569
    0x12106050a15030605011d1608060a1701020a08011202011d030a0212030306010f2d2c1002070503121e04060f0807030623061605070e0703020f0301060f0e 68
    0x162065804e81d5a41c0d004000f20394050038008001c1c0d282d10032140e1180307007401c1800a881c0055038480100800c1400003083c0c2c0c0c99000403c0060f1103405d094030b18603031261702194080e52200c42d43c07400096a0f000002030b081845030b01081c41540c140c5404c44800c2020444185208541d00300540c9032041d241c1110260312441c3d080a0300c2d80d499809160b60b442c0000014010840d0104d41e40b00308221151603040f40d526041c1030805405148600420802440b03074116141ca400300d0409034041c6ca40205c0440c0611401d4154818842c241c0c4c448010740c0d15070303c05a032140114428940c05030007200302014860318400051102e850f0240d241e0703a40c051424402405500a60000c41c0810701d080c180000130f80d04401d40070f6018034503107010711200e42440e40400310f00b400c890300f00a0451199403007038256912082602ea48216404409850124a0a041e50740c1d40452007000044c0c107000012420441c824021640070f100c03912541c5107564680802202c40b130404000100800000f0b0f111165181e03508 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 714983057 1250 714981807 714981809
    0x906040209150316050c12070521090310020a09090b03030c07080a0302100c0e011d040f0c03050a05040320030d1103090118020907030e01020c120c06012106050a15 72
    0x3800b0703115107138509281c01040a400389964981801010f220004042e0b20015070400c407030b0310f000302d148e84030300852403c2c602c0e060100d12903900c04d01411440101e12000e40703028214240c1c0450884140c0040302c52448205d00c01c50040304001030700d0303400520020b441ca400484418070040c0c100c03440c00c1c800038480c03030034110141c00404407500207840f00c0040c5641007010220070303980f20108000c00380d034100d005000d80b960b2908442c1809251120300c800c40f20912031072514150042d109202e5001c040d4140e60040408a0150300403e141001003891096140704a0740301c5e99050326020f109242212604821060320480d80c1c00c2071004200e1080c0c44880c50151141c04060000007070303202c0c200b0140c0d2500350f0b84c0141c0c0000601140c4016800540d6441c0d00072a003050307130390070005484150000a90b02901c01d65507240c1840c841e01e40c56507407560800c00101024a010307c103440380c607602c0380080c0780000b413201005c0306a118078480040c0410600da100980041041100240d500307000340100d09130102c9 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 714984307 1250 714983057 714983089
    0xe1504050c190602060a1a0907020304060201060602030903070918080f2109120309011410090606090b1905040e130501110c2d0a0c0612060302010e0906040209 70
    0x204100d45011030410008030890b0300d800544846901e42040c000a58404d8024440c500b0180c481424025a440410315141240300241450340c2c00c2c541100040c0d9664803610500005600e0000006480351011040e81d0502100902500391249044500c0010b440010883c00b910050000307900c0c00650420018007d80b08034400d034541716450f81c0a5003a44cd000a11143c10255801c410440481c0c030110b24504840d00c01c6206513120b440b0758000714018080b030803605050000c61000d00c480d503c614010f5a0843e0401101403080607107032602111405210321461001c8503081c03040800c07540102100ba0a84c1c0414900641495560144486403040950302040c11003e07210840702400b20a006040000c03011090790741c50500b4019010341c0e101540c03400080400507184006600c10140404010050302d42d60490300030380d1107070410324106c0c440c1e80314500208140b1000c400c0d026400e070082c8401c0340d40586030018040c520000f800841d000c000d01ca00e40c4203a0030800103031203a449694000354002 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 714985557 1250 714984307 714984313
    0x2040302091b0f19200a06050a0b03030a030212070905010206010303050c0c0607110103240302060d06030203030c0607020c0a03080f0a031e0f06050d0b160203070605130b070c05030d0e150405 84
    0x184d002902c0b4070440c50701c00340199100c2d000d07a9807800e4005a00051240c2c0450000b40075a201ca0061005041040940d903041c0000500d20b001c1940c0b54001e0079134100d4603101c002c11900d6000c400d540302002032140b6805078000c00c0040010a000320081e1500d04412015034001c1c400c4100010100c0c0d01c40b050481d0740150314603440b1102d580c1441501144900b8040700e00c81213500d9100c04502603424840241314144c00944100c040e10250003641c01507902500312a202da03614841c8075107440048070702100600ca071110032009031914042d80c4013266004070748545002860a800d150507400361000700706054407902101c0914800150341000d5180002002070390384420003203c001d4800c558003492041070f5004281021500004c05a50410b51130340c80c060340b205000b00242d046004010340600b020349007030200b0085104a030700104269200c0c1c142a4080c0c0c5d43ea90040d02c0032404901d0144c9294010312501c14181c0081c1e20805c0482480000c55900182c681c0d980320814030100e600f110190 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 714986807 1250 714985557 714985597
    0x9091605090a0f0e090c060904020702010908030304060b1e011409010309050607051b0109080d0209010c0804080303040308070c0c0e09030c0f0d020c010504031709180a06081002040302091b0f 84
    0x13445440040d00201e03140003a100d0025030100042140c000c101100c1d20507a400144002160f0264400c0c000404001d0162a282d01e02820584003c00c41c5c4241c1501914800c07041c603141e0004080080d041c000161650141002050602c1d065500f01c041c100d410300d80e817005180c001c01e00403c200c0f48622a5075641590310081100300c843c01400c141000400b681c10f00380c0c01d41c0080c40100c207a42c0d405403040da005840e0385503030700102e860505070070740541210b80000b4040b0394140003000851145000c1e0311508900e032690b8004980301192020044d1030110403650510008100304c4072541c011400000326403d00c3c507062860313414100c0050b82482140d1003046140801a014030401031655000d00f400e9050903c0c50b220702800c0b4200c1c5005001d0f4580c001503081d2544d0f541442c000140021150603901442d041c82070100810342802003505d01d11a2128030350102d040d030b000321415aa800f80c4804141e4070303548003502c900c07041e441d0001500c0c14103001c81307200740c01e80b0006850300e2403121054415078 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 714988057 1250 714986807 714986819
    0x2104030b2406070506150d051c0905120307030f080609150103270c150903030305100b16020306010e150d020303070602131806061b05120301150905040209091605090a0f 74
    0x180d85086c1c0300600407080741102c800840d10205a8881202c000d41e20b120080c0d9800b9412034070344003690801359104209080e80d540180001016161080c03003a1242848c1101014090f50500701c1291095841004480007403130351599130040d4000340304181404070340740710005401144542e140c6248940c81790b2803008001130050340803005004003507003907100290200c01400245104d1503400080d05064403040031074140715880346a280207051410344140c1f50311000c508480c406e800c1c0d0905a06c40d00c6820000b00c0c4211945e180e45008034a90301c1460b1103c10080d0600022294041c02682e0500050100078082032440c001040130407a8807107289480b5041210350105c42d4000480500c0302d61038a0b0060020541011030300410f071010100c00c0080246900c0d14602d4a14518810068180c000c400001c0d400012881150040703003a8660541003038880f4203110490040c0607005900c80c40000109a001c201c107c207881d0484c03102c2c54010b140510920204901d00e0340c950000640c00550b4900b0004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 714989307 1250 714988057 714988081
    0x90602030a0b0415060522030b0f010311090c041a040e090c1309020603131b090507200d05070c0807080309120303061e010507060501082104030b2406070506 69
    0x200c0e00034404c1c2040040c2003c000403c0c500400406420161030140081464544102c10100650b480b50070000180f815140d00c240480c000e10044840040d69004030f0245d103401041c1910071000d1a00702030034186862810380c002404502441109201007101040002c080c10f40c1c1841011100003c040c91310b98038041c45130800e200c0401034003082c64680d021006035a8001240d03040305100048100300c140b207052140c0003990b141004010840c0350400021104a0ba8025074815070064660500c050306a02c5a02000c0e24400040980c54014090301e081e01d43c0618003428540c0d0080e030502c00d040d52511403092420200d504a01110752000c2520070191801c1c448010f2501c510700091400c509201c1d001c215400c00314480d281c0303501040800c050180e48104d00741c44616070482e0003030005594038206142c5490640c0c500c4000800d0a69494120b660250300700c07421650320103100d02c01d40d62814103170a0842503420091504e180b03800c0d0031249996604018000351401031000e0082410240543c043c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 714990557 1250 714989307 714989321
    0x1308060a06141e090408040506160507060509060d020c030405061605070f03110f01020c04091a100f0909020301020d2309060114210a03120e01050c1804090602030a0b04 74
    0x300c03c550008410020f85068000103d0b950415204e000e140c0e211850003120600035604850f0b000680880c4000340758150980b00e44500e03000358242c91030310380c440908961510034802c001e234000e24100020485400564010100d41c40ca07101520300b0542c9400005003558000d01c1d2001c0d1102c4500311007424000288091401440c2c01d03031411900501e943c0e40c07003150700c4628601c43d01c0f40b40104422822a4000c0c441686040c0c4003d01c00c101c9a5030f585400800540400c050b280c014041c031000507030720400f100c0d10314180d17031115100c0340c685032030160468082c0c04103a800301d070995000e0141d4030b950003c0e8000c150705580e0b00442032000e80306030303008400c0090001342604029404840100402c070803500d02442c3d0091700380c44080414450328192074034a40d440000c00c20601c00c520a4000781984064a0300007440503071814065901107040d800d09039102171742d44072901242041080303811501d041118064150203040860846c4858980c10201d8008407072800c4500d449100c81005482e152180d49 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 714991807 1250 714990557 714990559
    0x2030307090603020d06030204051608060d031e050d060b040509060d0b010513110a020607110d17090f150612160608090a0c0303120b04051b1308060a0614 68
    0x16055150030032008052458a10408090580c0000c00804030020394020700091500a0404d00043c10004810039001d42d0000c02c203000124110041800745c80c04c403111100e5660582d40f203030414a405010b0725810406005000144003003080501c4400c0000d0169074001d04002481c240c4070346c501018800d0a0710000c0041c1e2040b5104002100018800821541902c00c00c0e031300f1460007260f040c4c0740d10040001c503010010650001c5505511180d0000f4424030030301c2c85684039012603907030103100c0d641c40b44404003d41c0851030100564201c50500d850150b84071074944115010144052a280c1c20200d82c580e490310303e0341c0300b041000a58101582d4080c080224503004290214030040c0f03110180700a8001c05c0100116900894000001007055245030b6030451400c4280342c8d0b480c900034000d81c46507100303610349505003002c0140d1751800703210742e612812038151204011034038940344c0c06403030740882840030450003094408195440c0030450b80388907800c0c8507030003e94507050a480d801c19901d4001da031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 714993057 1250 714991807 714991813
    0x1801020604170306030307081605160e04082a0d08060312030112030c0503030a0207020f060301080a060b0102010e0114091203091e0c100513080303010503030f182206050102 76
    0x120000070040410242c24155600c01c0ca5100c1d203d410000b4210311175010050050f41011600d00c4503501c0c2032907251000ca101d90201d4103450700b29020309480003600d205c1d84a010280c000010049003011300245040c0310390180c80280c210040203041c151500c1d602c1d080714141d2001c46014811a0040e00b040e0b00440110b00910003150454002882480140a18172414101003544c0303003018003980901c11704903071041c00d5a403245818035070342c4025004602e007a8030980b9031045d252024144030003181c0c16907484c80050f0000700300585175007025000c2001d51604547d650541c3c000c0c1c0800030301c5843c00d480c0e8410300d032002c0307420031807140c514080701d10049581e2900c0c2042403110001d00000e024030b003414504081c05005a080200a080001c00c40c6160b401c0011509541101c0340c2c8180141408040341c0407030f0350315507122403286036680400d015041c0c240e8001c201401c03001d5009005000c0c44a030300010307128401740a901140c200101d82c40014141201c98a10010a80e420300406001e0102031000b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 714994307 1250 714993057 714993061
    0x709050c07031805120d030501140a09021309050106120e0102160f17030705190e0a181d0a0b0901150e0403022a1008040f1202150c18010206 62
    0x244200da10040074810070103481c4001480f0040300303038004c0600a1200702d00d060882c0900d51035210418140780043c0c13038200045440d40c164103110404000c09000c1140050500420000940c0080101c1c0c1140180b8400041c01d814203008007030190450340c0c0c5100001d00b04180d0241642e850f2201848140d00500c4983c0105003c0d800c8802d1040d00010030654a0b00b150601c81159040003d83c0b1202d040d00008101d8025003202c02041e4040340565a40d82c02408444100c074010f81401c0b000d40d0064014108000251440f400d4140013034281d9000620b07400b080350300022140d0201c0304070510350019a4840c00f40401d20030080e501801c460001d1120000c1511043e46000c110300030011103521040204040c140b003007040b00d000709400036031404400240000d1429520b60041c0103031281010307070014900580f188a0083c091648403251038234801880d655400b104d00940d10520440c8203e0403280b48030b0180380c01d00c3c0d0207064203800c2944e80b0300d134402507003001a02c03041185d8103550000003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 714995557 1250 714994307 714994321
    0x90112050408090603040213060f0f051905060d0e1c110708060604050406020c0613060c091a0a05090306010e1005100e10030605101701081615090b07050f070905 71
    0x30460f02003107022500c255890341e0f01d00c00070303c125118000c0d100107640f909401080d00c00b0000e035804c040e075522110500246603608100280c0700a0a420344a11540c100740801503800c101d00505580c0301001408156205482d00c410b15001101c007100b4007001892102c44002604440841403030700f015005000d41c0e90400c05442d0762800c0c040c2c00d4a0040756500005420f00201780d050f908501c0e800401c8d0341e414184044d185109044030003090b1507207484c0140302c2c881d2500950b4100200d80080c1036003c0070000e4030000f42501e030400740d03111087c8401040720102b076940904c03555000c1c0c050034a0740980c0c8d05041c6200348a1140030b4004070301806a40450005c102e4022035500c6100400721420140708540341421070140c90143c1c041d81e00b02a8014441c5009900b09034641142c0206c1c00500807141c1c1d8900c4543c2e620380340c1c01c800841514000400f0300603800341da401c100e00310070203040a20642d1380e903291500155015441c1034800d81c01c41c0b0240d009440d0144030319001421104000e11140c10414 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 714996807 1250 714995557 714995573
    0x40b1507020f0a1d160908060f0c09090403020102030a110412020d0f06110d062306031e01082506050403030f020c06071a070c031b0501061a0307020f0303070507080a03090f080901120504 82
    0x38090040c00200303180011140e200d242b04071003070311002a040300c0300d038142407402034040c0d0130503240c030002a8100300e01071512407441c00544040f80e4850300902ca10301402d40038889807034059401610080086104076000c40c006001780e803118016080001e6491704203071540c004840964200d0300d6942c1e007031402c1000302d0001d0358540890807000c845980d62619500e42c0360030382d4900c00698140c60f1004d0707000003a4094000c20540c161050000340700c0e0000030601c0c08200080002e02510300850010710040c0003280c0300755a149041c1140b0300403181c80d400054002221500043d00448060310701d090030310b0a022071040266041300403030425548040c1c00c0e580107404d2074070303c203100c50103050f0400508080c401c00750442d00003441d00e05507000c8071a03003ca80c1011280c3c403c860310f0300903110b400c043c000201c4002003202e03c615420b542d400d0030a442543c03802200e500000c022402c040d02c9203244008075400020580781d41d407050004070350f2107045030005402440108400c1c414289801c0030803010032011 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 714998057 1250 714996807 714996811
    0xc0f06020a1a18010c021b0910030b04140a0b0712020a080c0d141e0609040818041b020a060606020d021c02010227040b1507020f0a1d16090806 63
    0xc0c900b200840da114201103211400d56483c0301c0d0103608101c000e41281d0f401041118800c14640c000c7c400c403440c81024090301002c199942c2588002c00c4904201080e0305407200d54000348606990740e901c4110711422031400300840c20a032803a1500c0014004210742250f640201031400f44002e5040c00c204440140401038002c0604080381d06c0003490341291042a032050030310780c488103007044036410700805002003402c403240501c050644100c0403030079900d07040910610442e40117840b01c0c5401c0a021000c00d00440e4514060b80080c0c440e003400c483c0c854000e110040340b41c125402010307036186da401c2c048142c41c510380c40038066422455203410300c1c95000c101e4600d0031003902c1c596a00d010003030f03404900a218641840c210398440f940182c210031103048006014203402c0b18180b0a582c000c0f01040810b034803403409141e01050400082005007401c090544850b00000d00c0b410005940314003003012908001e1401110780302070020840c45482c1d151020a4a003218078203c0401400c1ca40300c143c1e01c03640 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 714999307 1250 714998057 714998093
    0x51003270204060b18040c080108210f07080309010c0801081e0c04060807030b060a180b130e030405042003190605040c030920100309020f030102070c0f06020a 70
    0x288440102076448680001d002131200022880c0c0d6188150080c0c0480c0700b003103003030f280300b613003440940140e00e03200b001200e040ea10303007101600504190b8034400014102014160310f0003070b014882c0c0814042e0714006030001c00d006140b503d580c3e183c400c1d04035007140e140140a04c00d000b02003005021510000440141e80605070703440503002e1113200d403001d25000d9611a00c80c3e01906101c004160180d020601500300c0e840781c10324440729120b02c0c08010700d010701801100e520216560300128030a01940227150305d1500a00b610081b0b505800c41c0381c09440c0200201000d40d4000038003040f03141001c0c80764086150042d9440d00d1008001c05003171000f480058202c6040f80c0c131180c0d16034001e44150340a0b500420004104102c210281140034014112061050b61885008100c0ba07a6024035540c281c884138000400b6100b800401500a030001c0650f01801c0c2d82080d0103802d8108103031402d1000f001c40c1800350843d46052031030505401a0710b4000d8100e00b086400c060722120000c0d4541805238403ca503 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 715000557 1250 714999307 714999371
    0x903061515120216080705070603020309030703030b0f040c1d0406081b1c050d030605030a031e09090e031812062a03040b090c060901090b0306060403051501051003 72
    0x40003511540103030080c0804015004d4034840002c040040f070784000c020300d500c50403d0300c0585545040c10740c124001111118901c1e04100082000a03200b58000220010014031f054904403000000c10100d0f1030740184c0300c0200b14120541d210741d896403030038414802c41c211000c1c00214107100300c641d100c50242d1b004400307180e2003c41d02050b95031541e4060004248200d0406548205c42c1401d581e100d28030300c52000481e00e04807010500b810b0100743c404025400d501e03580404001d00c840d80b1070100085c1480403c0090482010860510368090116034418000013552a2801000d40c05c1b040d00025072500d00c129a0400400041e11000c60010380c4007042034140603012800c90500c0b240d010416481e9138648000104100401246218840c01000c1c1c0c00121380170b9400600910800340308001c0d015012650302c110401c19070558100a69002c10060003650034580d517a0b0f18180b03080c0c0102c00804103000d41400502c0309080004009008601d1454284540364000d00c41d061088240e800021002c6c0d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 715001807 1250 715000557 715000577
    0x50f01120506120f1c080103020d020904111c0c05010206071707031404030f0801080f030f0f040506300621010e0d090501020f0a1110020a080a0903061515 68
    0x940d0300300f015003c0c550820150ba40002d060240300351282c0740b10002e2081c22a01003090030140d0320984095050ba60301400a0503016510340030040715507401030089a92154004900700c0c5602c072400800c0250040981056902e070080c680b0150030016508541d045500c42020000c85030b038891006103040084a0350f5150f07584030400c04901030620303001958200358a040501040541c480010068580c0342d90310900c82d66240d9054944650f42800001c0080c0e0080c0312600582e060a8014201e266172141d0076842d25070b0395004901241c11103000e0180d00d42d804010301401d5412009070060601209220448514005001035288001019802000d0142c1840c1003544802548a400c06030280000c40d0841e10030342500800840301c50140300c1c018080d0442c9820b8000c4009000b0f40303503a901c20303081c043d260104000d00c96040340c11a0b48804511401841c6000314108a000700088812942ea41c607a060035070a081c800c0d04e034030040e21215007114001c1000a41a96030403000c02e030712145040e007841 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 715003057 1250 715001807 715001809
    0x60221120c0d090f0b0a0e1203160c12020607110304030305073809011815050705130b0a091203020a03050a140313030813110f060d0f050a06050f01120506 68
    0x2001e422200030089402510482d0a021110310114400c0e580c6c4002489000210749800e516442d070162080c990792814401318a480440d0036802d4125041c520b4080341104880e100c0e080b1140401690101503000402070100695014444406412680c4006c502d86407039554020282d1141c403038050700803000130015807020786260038040300022940d00e0610500300c0540c07548145000070f03100f0000702c1d0300e090404007041c02000260222076800540312a0802100c40c03040003d0640100a1010450100001d96070108004440809030410400003030b20b41c40d002c1d0002e04040d4060300030042207100b05040c40300095002540d5041c6942c5440c0c203a03100d5a034642c0c2560903009980c010314850314040300b0411500e10401d9140c1c10140280d44070305841e152002c10741c03100b0b5007500010306540700707081a54020307040000787d490005502800305481c1c5280c1d1040c460840303044521240c02c2544034014480130505a01820303014082c2142c4102c1c5151404001a001208000366203013401d1701e5000207601 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 715004307 1250 715003057 715003061
    0x3020a0222321b1e0d1a03011104030605040c080f0102030106080609010e0417040f060507200a0902032211012d0e04111303032c040905070f060221120c0d 68
    0x84c01901d0b0041e20758812800903000f80442215900c64440d40c4420060303145414051200c0345141d031000c80785001d0460b103528025010081080d544004603200010b60101c003000040304016014000580365410420020a5086e02600c0284078091060041c0401030b0304044650f04550700c0307107030303007540201c00ca0707106015010741d501c429040c680840c000150b454100c001090454451960241c001403c80c0c50100888903c440f0150072070080d02c41403060044a900940d04407803403450507414007013400d40c1e210110b042031030103c52122001300103078060750300403413816006007050461024030900d01c031200d4202c40d1810382c040c0c10401d510f00040510b032141e030701884000305a055455134600d01c2d0640c0d002c500019100460015444071900003102d0881c000b1040c500384078440c02c4801d04c04070b00801000d4031401500343c07480d0190220000b04400c00c040400010b0000360058200c443c008091003814141d2407002550b034003000c0042e96220040c00185550201c40c00b903181d40c680c1020141c41c00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 715005557 1250 715004307 715004347
    0x11180f06030c0d05010f120b1915030b060904050c012007060905090c0c19240b10020f06060607050a08030f01050f040903020a0222321b 60
    0x500020004184411242120010400c4042a41c3c092140e41d030f8030a58068030142c3c900c203501001c0240000700300000c41280895402590240c2c4a6420303c54440c1c1e000300329142d040420110010401e010010030180300c40c000e6000c1e000316031480c243c0ca0b00707443d46a1140864809141042100000e844d8a103541c4030b00c00b011040b155007255500c50325040050309034080750003038520031a00301c40007d0741c46203400b0841729000d072800c003d00b1140781442c01c00c40a46019036402c817040d580900c1090800c03401c0c4150b0800f19074411001066007161750041c00000d440d070300002c03001c54202079213034403100c100000e800d50042010b070740160750740070b0904041d42804191308005207051030000a00042402c880c10381d50603108203c0e58440c40e02000d00030132045480d05407000300960454061070300540760000b541c02105400303090004500d207404890380c040b240c0e01c218402c0ca07648242180074102c081c510441e05a864a40311400042c1005000c0c070ba1608400c0b44001803201380045d14401480180000103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 715006807 1250 715005557 715005559
    0x15182508151b0d0213260a080d0b060703080703061a040506091203070302010c0f17061311070f17040b0319090b01060203070501290d0611032811180f 66
    0x151248001600b0500c19101d0b4420100301c00c0c440038900540d40300c41115500c600210100602c1d40d01c94513a1350184a40107410321416040d03859074ac010980e100c6100070006c03584240c0d100301280c0f4109030b01034115800d540049214411010a0004c0c0c204000d04840c1076480c1100d940e40c03101c0301c0c0c4000400050134903400c0580c40c0070207c0d5030f404041c2c0541140d15100400e440b00c1030218201e2908032007450100d01d02c000c1101d5224003042326428110b8041842d8508808042041403907100d603043d043d40010030440e10030381d01b81d0381001480101070054480c05005c00c6c04602d090706c3c0130310084944c00b018202d4a5032151000006180d1a82640a8034015a00c0040401c042da902c41000e5103d070402c900513225542041403428141c280c4103440c1c04101d9815000700d0581041c0d205006210010301c104030780088d91190500080c0680c203001d148200e40700040814044c515045c00b0b001e4550580711321410a0820100054123030100003611542c4d0341146600d0902c21104000607203d001501150b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 715008057 1250 715006807 715006811
    0xb060f040315110a080f040f060e210a1e09120c030b131218030b0c09150301050a03020f04020910030e190515182508151b0d 55
    0x41010100c0344421a145050b0200845100482070440c144a4490b44800241c01c07a0006031032982c01849450f00540109034402d501031056403510220740e03003519038851a0b4070018800f00e1a540c007100c0540c00070511b00300345040c48150080503010b880d00b8600c1030b0410080c0c4103840c3c00140b20b0441040204055410321141220a08091500a840780800d0f40c03405051000110300c050001d4100300c02c1ba511400302ea044c90000c080880f03007140142d0b80c550400703154000010204003440d0025000e480a081c0540da60242da0080040100602e200c810103c00f061004200b155100050102126019100c11440f0039240000900a1007200003040d03000300302d441c0342c0144a07415070284890350360001c200c40c881d43c2c80c0910300007900302161004040e507100440e101c00c01d84030000d465800011209080d44060b103064051401c06424a40c9e403902201507007480d88540000c94540001010301c40041c10301e07200c10803211400ca1070300801d840601e40b42100c82951050750351017110008c180407141 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 715009307 1250 715008057 715008059
    0x120a0b0406270f060b04021e16020a08010509070e190906020712080118090b1503070f06050c01061a0a0c0311070f03060608010b030a0b100308030a050a150501120b060f04 75
    0xe940c0f8106015039840d0303e8100c5580d8541480d208403011405030420007480020862108091644240254468030300c030b00440c44016181c0b103151a010b01302035070000c106407600d03100940c41c1c02c40980c0200e00c0c0810240c280070802c2c0c070700c58020140100ca2240828221880e0400e0703c0070740324451000700190813402090500300d038441031140c140c848030041c4d090a51160400c00094980c1904042c00f2101100c01081e41c640c68074103048001a4040c0603a46e10070f03a07a07000c0401101d01503104002082d800618904200806c4c0314400141c00502d00ca0748805144403144050b41c02200180018484002004401c3c580500e20007940d1202520031545180c2e110009030000700c4003840215030090900d078011900110601844540203005402088440c1a5807101044040301078610703242a5015000030002c205002c0c000d5102e40c1d01c5000200e524106580365400b00c40074202281124030309458203100030b85c0d004100c4941885402c001103040040780000419602c0f074928400606000020 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 715010557 1250 715009307 715009313
    0x7050f010b040c05070326332b0b0103051c0305010608010509180f0f0f01020c0d050310080709091131150f0f0911030c0c031e0405120a0b040627 64
    0x4140c0c16409100ca1450301d496000d446ca224000c0140b403100354098020f060106043d5084810419854078803681481503004940300e88100d078100f078206448640100101001e0140c001050742500c0403f880c0800c1650b24140d40100403142c107000b6a070ac500600070200307840d40c16502500d6a021100c80c250713041d501804080e5907844211003050211070181c9805800701480610955001104810190282c541d40b514100c4540d84000c0081e0718500401c1d9002c41d001e44204140c502170402404005840d0415003003136030754800d000c80002e06c690f9150005822112240606800e40c0b8440011140307080c10b2504040d003e010b0342d00718940303183d501c0200003c40d030000d10141001c03150000807114585856688590556094019000c040c00027000824040fa0301000289070070002001681e08140542004503540d2181c8844550008030114060013203107000c144c0020903040510080403c2c2a050b99034040c60000100302811321640c0301142e091881e41280b200300c2248031241814000c1d18286 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 715011807 1250 715010557 715010581
    0x703050106020d0201021314031e03040504050c0c100b030f150105180f01120c08101401150e0f0f10030c0807051606150b07050f010b040c05070326 65
    0x4400d14005101d541d22283c0410b0040c07084450318181c200000406504040c0c0c00c01c6140c1c00000d840d600340c410705500340071a212501d60b46018410400285680310300d400200410348502405102080008000d406001e00c1d002549106618000c0e03c00f10703000c1c1d07070240040d040009842130391090f809070f070f102210712000903100d9074140e40040710040d4460b60b103201620a181000c8418100442d001c8005004240682040a05040c81005540070083d1a051107030b08018004200400d80c1e03071102d00f001c07800b01850308150301410380c080313440c600540c00740e41c010801038403094100d00901c01c08009040715168040c2d41644144e0281044050341d55001d0010003c10380c06001000103803d040103e180144200c0403200c00682091b00c112840c15a500c50b000141a817003018a1140c035901c40025610703c840001c1c1c5040d03805440a001c024a80503c66030960300000300c490300c100c2c40d000b020503413103800c5070503501100e40610380a250040c0704413811643c05908410b40059010304420880010304030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 715013057 1250 715011807 715011809
    0x151d03070e0604110c0a0f2607020a14011b05010209150a090e13140718020706050603010605180717130303200d0c140c060f15060a03051305010507030501 68
    0x940f030030001900003103030a040d14040c800b1102c6264000d080b01c070001c01e03581512005071038003409a250854003501d403204c0c019105955881001003000c641042549008000a8020715542d1031304030b1131026a40009261501405810380040c9510342c0b103106121095059480300d6201402000394800c1d41d0300401415045003100d81d0000320480c502162044840700c1e058042c1d10145c4c140c030123380481e5079042c550303c80704181c41c1c01d900c104000007464004001120aa140d4000001641e8481900301442500c0c80244410b0180e810300310100039545508026142c0b4807010394400c0c0d10b544400f0011030320440701941e840783c200e605005102407001042511b049080c42603d04000c000c5817030101d0203407030304042a40080b4201c1405408000720481c0c000e159007110318034203d0001d40766440040e4a5070000440192158000f0040081c510f29146c04244c102c25849403a82d03c00c009800040d581e03200d840d01740c004040d151000304030060403031401d900010380d1000083c0180d00c1c107540020700408007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 715014307 1250 715013057 715013059
    0x50f04120c05090a09050c06160611030106020708070b0301120c0f090212240609150c010606091a04124b050726030c06100906151d03070e06 62
    0x500c00031504e501902e1050b042d00d150300002800c040f032004000c00800f0341201c0007089401c0402c1c0c0440e00020070b948203000c1403501c1c0d035170b8858603035040c104000e01c0c00e105e0350031807040307607020b11018041c80c80900c041da4112181c004000c0d21a89903460304952080c0168030a410004104030042a4461980c025041400ba80810310840340d44080305094803441c0310441c064080700422101c80c1c03a05101c4001c00281e000500510031116100001c400264060992030300346940d1801c0c00e02140340c1c0110000c008001c1c5240b03200c1c0c400c10b150242001403003103205d840200050002d42c402005603000c401102010312025025185580607a05c2c48401180c18420a010444100b840454860740c40807055880e0080300605081c0d0a02103031441481c0014540315080305100107071580404200000e207140543c1002070503603400c10380440c6c243c08105811080c1440e040c14020b029407199042c2c07140d00c2d01640d141264031410392007190050201000c520503098081d044020902e0001100d099010b000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 715015557 1250 715014307 715014319
    0x102010b0103020306010804030c060204151d04060602150a0605040618050606031009230408040e011401050a0305100504020c0d091706060d050312070c050607020105090c01050f04120c05 82
    0x500e09004504912085800601150307000c004103020074817900105126608c10703500145031135120303a1349282c0e05808165800000d501d00c5244400c0c6c41085c00020b03e070304002d0700c080c080350f410301303070007a4940551b0742212404695100c005065207425400960060101a1042103400d032544951000741c6040002131074504d00b417502180080c00d00c0c00440c0c0c4508520340121170054200040500906000008030b00510441c00d8580c11500789070203100d01451189494a59031481c1c059a00300511059021464003d0303041d440f0305860b600001201e100c50f003540f4001030702da500c000c0124048112504020f40061010402280740f41e0000303800041e030b402e00d0f103503544010f03940c1f1a107a811101c1c0384202d886a070001c9000c030f03905040101c0c40034130252261050300c2c10f00c0c0005440342c00c0e080c0202c0da0400040d0403800d021080c4441802084d03003040d8944002e0000b85030404441d5a00c40c80b81da502c078100080020703252a582408820f41c3e0150661210114003500716007000b28807040c0324050140700b21 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 715016807 1250 715015557 715015571
    0x160219030218070206070c060204150c0203060a090f0308060d0b0108100e0616050a05220303110f060615040503061905011d0406090204090210020708010e010b01170402010309080a030506010201 85
    0x10003250384075440343c07045600601c10755950000c1103031340b004030050403600184c0038440400e070391008120602ca407030550703035615046900e6401010302d000c901408010803240f9060600c0046151420815125900b5080c0300444c2e490701c3d008500c4800750b6802c0a040e54990000101e0202c9000c039551402403200e4109000c24140f50380020b1b2508c0040e10b60290410b004e520a010b558020409040e4050741030610600f002140111040c1880d166954003e031182e039401c092040641011440d516207400e00010700d124801c4914007660b80c40301600d101d10807502d903440e600c054840c1c48200c80207454081d0580301682850100d03423a20b17201d45050340010a062400114081601d144c00610580d419081d8980700c3e1210780341c0c0d80c000c2000081c16078009031601e40010260325104013124048a403503005201c42071922032030b5400c4441d00b0b07504440c0e0364140b1111070f003141c0e03011810203a4400001e244000702d46842c40180c00400c3c0b03440008041140115452490b20303050703400144220f200f80c000307119030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 715018057 1250 715016807 715016839
    0x301140402400209120307170702130f1107060605030f0a02010206071211040303120f05090304062a0c15030203040803011203020a080301291e1602190302 68
    0x444a1000a5440040040c0340925094045050800b00c2c01040c80145010450340c04991050034580031602550300014000b000c0010b00d100070f80408140c00441c070704101c12540050b00a400e9540d120628580702c41203850814000d510103100302c41e82c00010781e914003080c03504502038a020b00c1480d00ca0b005074260000c0c2c09101050780d501c0070394142d000d401140d4800b030b0240c2d45400d800d01d503141081e503514404041007400710010000b0f50700a45400d4603040c0000c9642050f030702c0f55420940c409050806100000800000395002d84495003043c50301214403d00120090f02048038003184c00800705440010b12161261841c00d50305101060780582507404019010ba11003990010036440082004100d411402c00d28004040e01c40c0c419a005200c1039100d100c0143c2080c4c000041e102c400e203040c1010303c02a0008200c0440f0321b4243d060811428036822510344184054515188074001424410750364444d0030403180303e900a03e825014001c2d895014440d000300d00040f03024030040f502903210 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 715019307 1250 715018057 715018099
    0x906040c02060c030901060521010b03010b102304030809100e010c030e12010e0c0a0f0f03060c17010902120c16080a12111e03040b040201031a0301140402 68
    0x111000301c1d00180075540782c482c8105030980c0010100b2541d556181008030b15a40d41e4440041c0003080d2125040d030003465201585e0850341c070403826900c00c0c0e14040509203291a41c520b42d0b20425110f08142c88015800300c810400c0c418072040740103014400280c080308101e400c0011b01810b0b1300c02c0c1ca003221442104402650700348182104036002c504080d280800007442051032484545001d402030300c1c6107003c24002400e40b950701944a055030403541142e203160402009030070082ca0200c41207080e03e403400d00c0003000e1408500000d41255220f0b0001c0c07080500420900480e808481c6030440190303541c40400340290404603281c00c4084240c1d01281c1e01d0364030402555108400803107290801803503699641e4183d440b2401170801e00c10101100c008035000c5100d03004103503d810b1080d6650b401c5160000c0307440300d4280308102e01000103000344004201d0040d0b00700d80c41a030a0800252103190324500c050b0140592203125810f41c2891515543c00c00029010b5000314802e4491a84140100c0c0348001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 715020557 1250 715019307 715019321
    0x403030e0d03090801050f011403030a05040b0c01020f180f011706090415060906031101091802130302060301060f1d03150a3c180305071a15090604 65
    0x4050410300052031030003100c0303036420310711a040902c40c007a900c1c03003000e0030342e10200c408288500c8018010006100f140802180040c0214050361500240d1000545070303001310300900808502c08201c12401540950481c0e02c4500b2030051242c9480c46101e0b000304e031406d0f54440342e0085501c15144582540201515a02d044500700011300540c1c4103420701000781e41c0207000b900c44410907401c1071440c621a10a40015100010b408a081801d60800c41101503030410441d041003c981e008010259506c01d4881d5610307984200980d8612007040440003080032038002a44c030070300c00800010a42c0c1c200307140550411f45901e40c0c00e60300d0843c52604019040e01070701a5010741003032200702d1206042c44007440d80301c2034400c0001100f2164142c0401030075116001401c21440d14000c880c1039144008a0160041d0368007800d001d00c840103480095620200d040084c2800340104507101042403041a41c02c10040e8403501c41b07610f1524003010040701b0700b00c100300c502a180280220b141404d150082c51 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 715021807 1250 715020557 715020563
    0x2d02130512100b190e0702070302040f2007021804051c090504150e01050112021c020405011205090a23060702011b03060530010c120f140402120c091806010b0403 71
    0x740310b00d240602505c034480c0c000b4101421070194404c0800181d9a6100f21601d60801920009159082600c4041c00f91250750011200403000c6c40801c0040e0b0b45d507440c03075088450300c0301c6040190310781b0700d05140351031006240d0780080b4055400d103400300350303100480d4000c03500221004d0008500090f5403d0b03131140c443c010300c18070907408030050007994000c0744003007503540207c0300051601c07040c0c030200681f00c40d04505018115800040030031607507a00520240300881544820031060031710202c5940d844c142c415008001030b082004600c4048a0702d401e4100200c0305c28184c40c540d00d445c0000078004e12510007010342c409190300318440c060748039202e65411b40f903000d880381d240c0900c1640c80819025029182000300d40c800701044000290030301400d035210741d00361100181820181c41910681d003815030106142842e103c1030480e501d08003048690020340698400d10402c0b4012241810000031200050f0800c0d4100d040c401c11005440c0c141c2c00d42c10031304050381c61503625201381507164410b602c405 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 715023057 1250 715021807 715021849
    0xd0c210c0504080304090905010606110601091a03030307031409030f03010b07080c03070c0e010e040812040303020405030a0c0f15080712020d050109050402042d02130512100b 77
    0x4024014a40c0c032114045240741005030509035184000d03490340e8880e40011400d261902c441200b000000d004040103020302e0b04003200c0060980040c144d403800140b05211640f40c44100d104011450000c8140c03aa0300c2c0541525900c0c0b0305440060054100c021040d00e1801c4c1e010b00160400502100391a0b460104850003855039203003110810305030b004001c0c1a0fa080c4010010303842e000d002000204a00e503c00c001070000d8624002d03601910040507030011900310b440d84100000640f0400480b0120448102c46280a448500b0110000d00940e0405601841050407140601010f050100100c6900c40e403d0b02d0201d40700d05485c040c845103411600c000c251284c0c04610700700d000d000c1051080d8004a0300604250b4580591002c7d1082a8008000541e0315000e000035400c003401600480c00d030602d010503401c0c01e000301c5100c1501c2c00100007902c1d69030110300d0b800c401d083d5424020080200401e4182c10442a68025403511001c0c2480640540f03040100c42d010b04000001e84400d1081000e2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 715024307 1250 715023057 715023107
    0x6070620190806150301060215091b13060816080c1014070305070b0f0712060b03130c0504020d2408120a03020c0d110d031505100908010c03020d0c 65
    0x90b40d420001030101540300d0000c0351010304407110b01c80998000c0050b40d00400240e6000c1c4981140c0710000b0b000a081c40c2c00c2408100174001c0d18845450310800c060300d50780e6112182c03024000c010441900112203900a994402009001503105d07042640c200c98141d43d400c000e00000c000c0c40010341034a00003c0381d25030f0940d4099002e200c02411500c0e010f403c02624002450384c5803104d03110211005600784510f0f030140981c00f41d010b180306002130891142002543d007031001007002800002c0080f01d041c2e0030022208108a41409018001c1c00054400c0d501c610300c0701d0a00300684281504079000c00341200c0a8001d59145c513100d202203860075006030441c40420024040143c0c4070382842002e05408214080d222241003040400d002c40a07030310155070b6102011058100241c8841c0f030710400d410024060208001040700c2000c5034800c407080e9009015003d000e0b9990b050310b600a81c855480c1c80121000c90350543c00074038400c034880ca0b081121005a540a88207501049a15001a403507804 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 715025557 1250 715024307 715024357
    0x1d06090408090310020409090b06090405100c0c021806180712092d0506090106050a14030f060c04050907031b0f020c100207030c0603020412080f070206070620 70
    0x1004020b015000b50a0740c64240100201405903171140d486400010303503c592003400d1024584903160007403000c640c299480d04041d00c506564508800241401a5460070b1610100d80034803084496954050a68141300314095402c441142c800c41d08030340104d90452207405240d00a08595120303040350b46072803082440c0100a0401000c0001c2d0031240000e004511a1517000840c50358804103640803403140131000346142550078500b01411001040c3c2c1480414407076a82d403104140d041c0e0b149849040c0c43d010305400041c0c41c00311171058440c114000c90090120304041d000051043d500107035080541511100c408030106c41c5087c0708850032080c0340701d401e020184518090040100c2510441c1e4004141e440055444c00c030030900740c80513a1000c0010170412807001d048200030003040c04e0840c140781c035014020303c41c0188264001c06000002807020380301407428080d2480c040d00504100c1c0c60351001e244c130000070b1070541c01c0140400001c5040d480802103420032102c0e007400702e884d0701d40c07810480e0b0b03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 715026807 1250 715025557 715025573
    0x7020105160206090d052104050a0b091504060f140307080a0b0d0b01090c090e1b071b03150f06060e060c0309120109030f020d091809021503011d060904 67
    0x7140c200d80c800b034104181c00c0550b4403064801362290051018003a20350940328615014042038803600008802807008102e0380e650386082000712900d0725070a5598100741c4000541180703040700302405011010030007040310350740921700400b2612079841d0401c43d0001d2440448841c0000c40b011400101500000750000503150045900c0c00f901509070f0541036640d9503401c0d0202000d0b08000702c110b43c1c9424400003a0751024018000b07080d410126080c504040180e0080341054980c04242480000317201000c128a42c00c41c1e80f020310302144403902e49901c80c5054410001400750012483c2c1c181400f42400c64240c1c0f01d10011100c0c143c560b120000d6000c8180401c0d42c01441c0502c01500050104060703946429911440c0c0244038000040d0744d0a00e40f6003d8101021014440b04640c0589030354080d01fa0014821000d40300410b0040c260400028044009030032200002500141025960411807945501460603106403828180b03407595801c5c14480d1180044500c2644081510701040100e1452 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 715028057 1250 715026807 715026847
    0x92903010b1602030a052808040e1e13020a09290d0203030706060911180934110c0312030406021b070e150108150121020d050c07020105 60
    0x8402c0c0c0d04002c03541500042c2c14002042020740300c070380006140030a490401e4000980542e40003050301c010145a4654148500a0b409420300540030312000c80c0b02240e940c6581400030200c8445942c81e850000011000342c10208005c034002c002d040b002098080403400359100401d8032030090007c1d1402d641503001401d103c06c110070382080d0034581110141c0c42c18030040510a01403000840c40354682201075080f075540340005074107540140000c0f403404010300051008010211156a481e4031814180080f54031442e111030a210450785841407400c902008821003c0c002c1d80302d241b0301c01c40d0741640c075486928113a0501e5040e0070459174036003006da8a2000d9900300c0e008000c01400d0039518040e1142440604554a03ca80d12448080040071403a050710360707000c1c3e901c000440d5140744500000e8105040034028503118144c0c90304070a15648254050604550100c0e482c650b010070755440d040080d0310008031101080d0800b0001448200f00c401141c044940c107a59241ca004407481034101e601c0c1103 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 715029307 1250 715028057 715028077
    0x120711090403030f02040f14180703020c1204093e030408040801050c04090b0d0201080c1e0f0901020f0a03020d1101091a390a0e040c092903010b 64
    0x13890740000101d1031188040d002408075110442c800c036050010244010380099413031841105640000c1600784142a403440e0851a2401c015031204004a800790034070510042c207204c07541c40894001252902c6400c018003036800580620401d16021081311008100304804520030107015a00d002c629080340003c5620a00818031107003440e40f0b50313201074255072080e5400704420202140030720032020306106408245100b114074003402c0e109a40040c09100b80180384500072240400d00b00d2821490952140050345031030583c60742e4100e1000362695540120408500612903560000d00746a03000811601c050f8054000301460070301b501c03040344e40d5060380400b0b4100c0c3d502c991840e070008a81140800d40100001f041b1905850940b1030003603105003035030b50305807018a405542580c007905a00c1061102c141015229034030241c0c444142c0311402003032a4260441d1502c44481291a400310444061741d1114100042c4070201c6600744040302c0016616402c849020001040110400c000034078003051 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 715030557 1250 715029307 715029311
    0xd0201140d0b0301110a0f113304060f0c0306300510090b0a0b011d06090a030605060a0816060c03090b120f010803041a030a1b03090512071109040303 66
    0x21940011909542d4980849049607801094031b8280c56001003c0302d02851b82d500d09070aa406802110340c2d612208400c001203541d05440800c1003140708212000e403c4448107492100300d0809107008402040c040d2071803042c461519040114851290080c0340483c0c006090141000e0b03070044159104c0304d1380c020341c205101000790f03000e00014070610011485007a00800055041d0940c10000008a801428108c1c000e1919114031110703a040b8140e40380c00c54540000810504510020441e031b4841e46881d1544001c0d4803400004021a980007a841400103490904078980d983d12110354951a00c1c614141888038079800380b10305481004031021180c0a880e084125650b21200b11920764000380144c416030610b80e04000c4c4020458200da0300505031040110710b010b00d4000c8101e00040204100c1406c25000004602c540300250890092541c0d0074003007030884249400058020300750494110791a01403400c4aa60721a600d209031004940c200d200714241c030b8100d030700300844620020300c00c0341419 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 715031807 1250 715030557 715030571
    0x50102060105131805030304020a050f2d0409150c03060b190201090605040f0c0602030c070b0f0c030f0c0114040c05060a02161e0b04082104090f1a0d0201140d 70
    0x40c080c2e408101405d000780302841d500d0405005005940d4045e41040b8003074042808190415100c5131411820741c1041a42c0c440d007000c600b0f0604802c003c80c80c044940c42418003462405000d03800184806010805c102000300c0041014280c0607241244100711401c0800d0100c54404454010549150f8810b0700c0000303990001030341c81c10116a01039500b43d9141c02c0f500c07040c0c001c103c0f408400342e02030f0482d07000a60070b104003030300c1d400c0d0f452071a8020281020004520940110220000e5503c104801070581e0740700c1e04107a5405915801c403010040c03a560a001003556541031046825000c0e0340c21016101c2058103010600a141c0c0c82182d90000714401c81242d1401c01090b4941c3c0d00190102c0ca00e45c0d5042c118400b40c03030300c1450072a0881c0e0003010080008100f0f0907800103080606000c0401c00105201d04c4810b21030143c040c2d0340c00321040c0790030100842c45242c2c0c140d20020380e000106c0c04c50f4440411807001d0200c00c040d20b40c0c00a000c2851100204099140803000e0261002c3e80e0101180d98 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 715033057 1250 715031807 715031831
    0xc030c070b070605060d0b060d1704060201020307170105060a0e190b0307020c01140909060303040801060303021005160c060b0d060e0a0314070c030b0604020712180f05010206010513 80
    0xc1150703441000d0060300828200200611070113101d070000c5040382c62903041c1046880d00c03001d079034011300f00c02d104038011707002013081154278400140c2e035031040104d0b66280c1c0e82d03c0740064042c3d8012104000060141c107411307032030b140c283c4059078180d80024001c14203008001720180e5810780c04403026540418008043e40c0000e5030b1104060141040c130a40b01d499082840020b8070307080303020344c0d110305111040e40d031809d5203260242074410b540740840d030001560b140e40c0c01103401d510454211f03c450b94200f0394080289600000c0e1111424018481040207554a80500c910a90b0300480f5400182c00350030b5182c00f0030095001580c02610080074009610920b95070103080380c42e0000b0f10b007040d070001c1120406058004a81c0400708a00300341031498480320303a45103800c00b83d545c080184a192a03001290b444d8903a0b5066510310b40d40082500000c0c281c2000140c410035444968403510392000c10041a21881d0012800c22607006030020100c6900309000c1040c100902e0186140f1141ea0361f41c10403103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 715034307 1250 715033057 715033063
    0xd0203090919050a0603020406090c1407031403090105090c0f030318031e0105041a04080a1202090a080c0307090e191b120b0f0408040501121b0e0a090b0609060c030c 73
    0x100004c000008860b8a10b03c188415140154410b200691a0070410242a80c2103102e246040c00c501c030401e5500c0c405860f060b5400b0040d0380190b07880072004070820040100541c0414000c921000454062000c91b400700030728542c0207000580c040d0814000599010031110760341070050001000d580329003551403504207803103072009150f64907613455006000501850b21519002e20507082c4100b900e0b450141c40d14031483c802c0300040000c0120152030383d007840b151a81541c61202c80106401d110782e6a82500645d11100070b96014401d01034128000b4403100c89120b400c406e000340001816002c2d42280801144803141081500e8090b01d100000801d00560384e0008003900c40320300240b01d00c040da03082600d0035800060001180042c04005d201c003040424098904640d0309180446d0781003c00c0c542a0701601111055804180541d04c0a0804030f070050b910720409002a0341c0c5040b02c690362040203054984001c00700e03421072404c02074641036041607002402c00e0080c047c100c03840d1403110698103107 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 715035557 1250 715034307 715034311
    0xb03090f0318130915021809090a0b0718030b010e280b06070203011d100213030b040317010e0601030b0420090d05033f0601051b060f04060e0d020309091905 69
    0xd500150740036072120b002c040ea100c0c7c03101c141c821801600d0810601c659407928000d019014031002c0380028480c610448040c0c402d40c1c0161a42807a2a0b03503458160180b44003070003800304001c0007100280311420303805d140004151641c0c04619040000345600801807850300607003a0069410403500b4050707207090040d1070300301c000d00040381c40c03030b0055405203420a0b446045401c101401004425410091107041005407034000115400e1604c03a4a030039101d1040421003903c40303200b0710000060402188107190320511b4280c80504c0806040d1040208456071501c0d0740144408021020b2a501030100c0139080046000e00b9640d0900c4c0d081c1c6845103544c01c40e886072a07190b007154500803c041c202080c100052501981d200c0d00d08001c2e110701d4800540000d0420b810440041810802c02481440000500c0c0c420b4043ea201070a1107a17110080c0c490482d030030f4034040d06024140d10402c1e40040c1380110101194055030512914100700100c45d0006020f800074010f468120b145500c045129080c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 715036807 1250 715035557 715035593
    0x32040b03100603050f01120312060909063e0901021222090603030e01031a33040308040611030d0e0d021203010f0902070203160b03090f03181309 64
    0x40c103007480c0510043c10f03100001c021640c20b02c149001000b241000601c50018142d050900c0c5680c0408d9100c0c400080543c1d600c11030b50030781490310301010320515a01c002d001041144035820490300107240003090303191851a552540d0303800100c40f4980c00c58070001c4c0445200c1407058602da00ca840c10840545d07044030300728803801c1c2003503d800983c20107502044401440c82d20024401140746840203000c90019030001414107846003171071449250301c000e4458020a009000401c410401c01c1000c0c01c549031038820242c5001d04100d8250840e20140581d02166404521685440c2c00e0100490f4120070080d60034905101c24000c100d0501d0700c60151051424042c4004d1158940100000345040100041c6c0e140410042005010080803e1841030940d0105440507a81c0d01381440801e261440c0704501c208810404400441c0f42e140500045008607440c60494103c00303042180c043c1c803072080c5902e00c000390402e5650000a402c10044080c142c5011040001780c0604645911400a81c804400d07 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 715038057 1250 715036807 715036831
    0x11040e040f0b1905060126130b0c12010503010212010b0f0f16120c030e0f0a090e1608060903041a0d0501080c180f0f09070b04030c050f0132040b03 65
    0xa4204580f5600c038865201009107406540c0e144a0f40c0390099401c4c02858490b000c2001e0400654070f481282061406954407011552192502a40d400426040003188000000e181e500028a500d01402500e90b080608103107809103910b003cbc1c003800e0720b43c40074180e800349650038440d524800c8440000351905c00751910101018440f64031304014650f03004090b0340180801d502240000caa070140c40d101c000101a605406003401000025100f0386a6510080c03e023410b0008481c41902d0204030024000145405103101689800c0443c0e22680e013110032503000c0e4028003081042e000f030303a101051480c903440501454001b10070042c406542d400d0700700c04419400b0b608511014104442210f8042200301c0c02800942880799007c0d05003580600615031160b40400802c80700f0300180b10600007003000300c1010307035919602d1078120002c6101d8807a25216903c100b81b0010203500990032542011104040d112018a040084850b1215a00c900d814160000d005c0482d840400e0340c010340c000c909440403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 715039307 1250 715038057 715038091
    0x72603221505190e1b12150c0d0e0c030c0a060e0607080c03070309140409030203040306090515010f0504050c04060503191b030f0c020d05191701170d020111040e040f0b 74
    0x21056000313900c0c594046c010300740980c0340003c0a1001c80c110101c141640c1420420f51150f05d00364040c4d000380a00c078403044d441c0070701407280320030001002c0c5150001a003d4440341c00400082091012541c480c01e0007043c1300b081c068010385000030003842c446c0e12400b8041d080184480c041231950300601030850220f0f4401409102501a41c0001d6042000031201404502c0ac40d0f98000e40700d004501c80100419114600c9804110092004002c0f01caa484d003064243d680d40d081d20154002544515805149043e0114240202c40c00072030381610959150546180c85040410f45010b86c0c1d00e5040d400d256850b10f000b0107540c0d0340429844a00c55540d004203201d00406560030454020b50800d10540d4850608610511b80181c240c035002d0380c80c084c10948036000000241e441314400308090480c0364481001081444500500040c00c2000d20102c840944281d18164200d030111000c050702c0000503c01001341e0302810890960080c03044803a1140552180d459089130a82a01c955162900c031a030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 715040557 1250 715039307 715039333
    0x305100c1b052b03111602010e24031e04023607020106051215130f1a04050c0d0c1a0c030d0605030d080c0f072603221505190e 56
    0x8a40005d903201c1e4600b854048044049183c0c00b058150080c140000ca9260307250702c1d034940ba45180e1501c032102c5a91001d00008880c0c054641c8220f036801314403101070340c49045280d0610b0034944501d5001d03188030040c4842901d00010294a04000c0403034441c0f45081e0a0042c26203009107000384426000860420304020402c900030300c10000140c0940c2c88462102d21050080031340030307000880c2042d140f0000502d07013030125200520710f1000e01100c0d55040f0303008d400203105851314412406142a03c1c0440e000f003080001c884402a409445500c07680c8042c001c0c00c900040c481d100d002c0071215103261010315508103065070011301610050039622441040b26041c24064281c0401080c9000c400074580307100403001501541e45002e00601c1e01090080401c00144003d4520007194001c007014030180f029520460f038411503610f00d44640e00c110303185030359500100381c6081e281d110100803e00265003090750300501004102295103140e605040400806912600c0803401c18135020340000004a0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 715041807 1250 715040557 715040561
    0x13030b090c03010213120302070306140711010504030c020108090705030f07062003031506071a0a0e03040303080f1314030a08060916030b0112150305100c1b052b03 72
    0x714100c1d000740d004008074885030128030500750a8411003800c1009494003418101c0c42c1c2950354000030009494041c005412240086000307218402c0f981d50141c0c0c006603d00703100e0a0302c0090398018003165801c4c1d0079400640c004c500481c0e00410823001c64591710303520b00011f40791043c40540801190800e500600c4103aa01032071881c07030340c040020b90b0340965242581c466503d00c001046222100d8442d00300c04641d56811048820403500540c040c42084141c05a2a00700707001a22000b040b9403411b00040341c03814000c801d40c2c00300c0b0b42545035001c032662003000f0f4540121004045020003140903048000040d18581c0100e101200318000f10340351502000007500c0c00340b01820441c89200c010040118200c0380c0c0b83c1220007060301e0301c0c3c00301d49d4400740740c016034200c0c070704038440c001030b504081007482824044c0d0511802c403401202143d0540c0c1c2d444403005c045a0082d180034000803c40c4200e2250604002600c01c0302500c50f1040702c600b6440f0b046200b020f40e6003641d1041c0d04254901c0300102007a458 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 715043057 1250 715041807 715041823
    0x140a0c0810050906010b130b0a03051015020d030e070306090305070b1506030601110115080102070209010e040b131103010c050a020d0806061b011104032609060301051513030b09 78
    0x441c4003000325081000304140e44074014030418152280c0041c00f00006036440b034540000f8041c1d043e900d0f449002d01480540940402c07907462248819038403001907080c07140d524207640304034140c0181026620b0040100d0180203003c01d400d44501c0745140020000d00c5074410b140000d0f000b540d905072903c001785007201c1030030000341402c4500702c550012841290344003000c603500120242014095005845015405044104070240c2070740414400095001da06400601324284211a40c503221b80c0c03565146001ca440585001d8002005400028150300c220030680074501c1c020601403000c104030000080c01d49411a07031000000302c001c600f011840e50100f0009a024185040040c0149412004100d4034041d410400d0f00c0c3c884c0d40c0069000002080d4400315500030340700c0c129507030b5640f2030030114042d40c450340e1815424020581c03114140b4103071605a42c10f00c84005c28442c41d50b41f0705000c01058011841040d058901c1c00c206170315601e49400340311303c011803003024080d1451130092029800e100c91 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 715044307 1250 715043057 715043083
    0x1140a0c0f05060103081e2b141015111207020105070c121205070f02190b070c06021204230418060f050a0218040908130b0c07170a020d140a0c08 64
    0x414400c540294038001e00c0141440002345490340c403240c03104461405041c2d0b0b4205100b949040d03c040c0241d0070706400c8803100790b50108507074414080013617408641c98882e40e0b000d00b15a4105140c541041817440c8014610a80145482428034040382c4841c2101801c0b64080c0040601e00b464900800902c51080100d8000e9800c02a0415501da107076003111068240e0020b10030560146140b45c90404044100050034603840d00b0341e1112518a4040c42008450050202501c15483c01d8152030b1007190840303055800c01d0300b04025080104a0300c480781060201e2443c2d0013911100503104c0414040c2d18000b00901411000c40c5040c0a44417120448402420550000d801086980f60030100908030003180e10007540c002075950854100440c00b40510703c4039003459200d001c000900340c6501c101510344a0301c0102660030440d1b46e1724200500c410400c40c0741602d900124000000b40c50305450300b2203c41d009065071501028000034031410041c444030101d0f082a200c1c4003c1c03094850400054080ca21 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 715045557 1250 715044307 715044367
    0x110108060d151b020102091f0504120602120405301606061a03040c0b0301030b010b13030525050406031113021c0b01020c01140a0c0f0506010308 64
    0x14080045120140340c040042c14001a0244070680603080d40c0c4295101c0c591402c040d440095032100007801307944aa01801d20a403103d100c01e558120f490710b4030b180907407080d0301c1e1545414945034000ca06846021070584140ba800d102c110b9002e407454000310b105070301c14006015400a1408181614104a40f9034400c0380e40d1494200d1300d07120054111a000180400c290300c415029191060203400a07030041d1402c101e0b01c040030b41040d40c6020246008a10600400766203a0710303906095001e00003444003421b15403a100c010003990300540700400c19504051000441c19031203485007460700054080c00300d215440c141d80049404130251750040505021038051095510f5500ca04510b00b0401680600c140c401c80350f640c0e0200c00039030482e1502030300c14060215800b02003102c41c0042000401180c09070040d40441c1c840f80d03118807003c2440796044100507003082c0c0901c200b00c0d0208290f00048900f110400f0030100400c200700201402107214114040d80d408603c1c031001854142601d591403503203 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 715046807 1250 715045557 715045561
    0x1401050906010618150302040e090c01020604030302070618230a020607062d0204051e0a15051c02130b0a081909150c08100302090c030a060b1204110108 67
    0x1034007080380d41c111000c9240280444004d110744100d00c40c05540a54985840b00341e03885103998160f00030f40304903101c106611a00750341c3c1c05013103030b228101d0080240c0160001c00014000070701a03070240681e01c0c060640001d00048450249042800b400f5003510300880048a090310030100c0d0b403a030b9041840040140c0719107502640402c01c640941c510080c0f07019244c00713401001c0c946103d01d03642c030800340c101c1400149404100b000001c0d80b0601480e0b00494840111003146a102c0c07030b07845e004d65809440501840d2901c3c550295240c204540311040200400519000029407542e00b11001c0440e01d0040ea034110f1214101d03807101076a404880c1c1c004081c0106100e42c0d0700104031560266030a0509042e02d4015010a4000d101401c4010094050007202106400d480c0d400b00b660521319846038441a22042c1c0004c0c0e01400780c2c400294003804c01400079001a5542014640007500c003d030108140c0d80b91801880c094111070f0700001c40501c0001040180050119100305040f402e0901c12864 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 715048057 1250 715046807 715046821
    0x40501050a0e070b0c031909031106040518040302030f18040606080f0403080702070b1206010906140d0b04020c1e070b040617280f061508040201210c0c140105 70
    0x24200c04d2103012040e141c08541c4003803000c001d004a540742850f410b04803651000214000d860441070380001c3e01d40801d0441e4003801e03418004119010340700002d006040340a245030101e202404010300403011404140720804d407450b0810017804c0745080d01c1c03036621034081c1000207110844189034400400c0250110912441c11011000c1c2c1790400c0e00b40c0b620303950310b64980300280d14211f2268820002c161001034081256103c117004c1600580e0240d94101c0104c0c1d0b01c01c82190017141c0581805a0340c1e408100c00d404103182e0b58024140480d000c0c1025007000880300085040c100c601e840070130030030010340841c2040300050004030040d204081d500d40c203050a10360001e114000f1000c0b0001ca40007510080707141814000c071501c050314450301504103190076051058020b03002580c80c40b0403403400d000010440c49550484002104410740e50035203140c3d55900116400d0310740011410341c400907000d40c80c1690742c850145040d24072094480c0190800c00b46170405500038060000c0703007507902d812700780503074 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 715049307 1250 715048057 715048063
    0x12090d141626030703171506040e0a0b01030902130c0c020603042301020309060f090c12100c030603050c100909110a080c03161422030c060206070c0b15040e06040501050a0e 76
    0x2031011030010041c1d87e488030f8060120859507400c07580400301060004482100c40c00980c410510f054081c80303861040b00040d804c1e11105080298010008403401104082990040c01160070924000060300002c1d00440c0482d803060760b0a5034000500d918940a00c403a0410040584400800031440c524280301450340311000034107614203101a400201307a01c030000300074450001000030981c03030720402050504ea0392048118000d4001e00d0801c2d8190100c2d50107482a1021a80c010b03000d0540d04841500304004103044040704414004400b102003032800c110311461401000140845680ea00d040711b01805940c0020103d0f1a0140200200305d507100000d1611810090982004500700b028a000d40c1107901501c0c1070810300c4000d0328031082a1049107840355040301d010b850501910350700c40e41e0807170329181c04031010404119800c1c0d01c034000a2425048035849403a20f020b100480c0000c40c001429210016120122a4040c070284000e2080c01c0c40741603005042c00f40c040000094000030f09813 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 715050557 1250 715049307 715049327
    0xd1e0507080904020f0a0201050a24031209081608060a0e100b0312400b03130f05060609010e1005040207080705061812090d141626030703 61
    0x1004070408a100419922190144d56190500110325915030750031180081c001c000c111508030400741003580200505070380d0b81161405000c544c44400c41281581ca56808823a0340000075820804d41d1200065000c00500121034004200c07664078061a250008241c50640041c120b03408642c500f995040502c1c0000800e04a2a0742d07074031000c180c0b56200c1c400603061141010b000026541300240c1440c1400c03850005505825410081c404d00703e030701c240b0041707d4861103111082d4400e2035070424000c05000c13502443d4810500380c82582c60004e10764601081084c10340e411580360780300b0800d1144614022002c24050500301c005035545184c00381034101402e90a00c643e0380201d500090100038030001000300d030f4a0f60303000b00c2110018140205a102520041d41c0590400e0003002400046258448126880594010001e1002c00c5240d01c0b18000d038a1300d0034480a8510441103215a4400c000d4a04001420a0029498001841802100c0508a03602d00209541007041400c001a412144000c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 715051807 1250 715050557 715050563
    0x30b070503100509040c05092d13030c0f23060a2009150304050a030807110606130e16060908031603112407090510080412140c0d1e0507 60
    0x281d090f41783d80c05c090050b0136068101d1500101c6040412214151101d240040d003103440d5040a80700d41d000710300c84080c15043e604003c0c600050261b041c0828418000e10311218040c6a0706c2c665061145d43d10000d00070150340b10b01c504407441064040c480800c1c0040d640c4050150f00a10100501c3c841300d0740345181041d2042e6501001140f604900d0703c0c1d83d181c2c50002c401d0207004a039603081500b005941c450350404202d000540c540000342003140f08403461042120008018251901d07200100003e8002d044120740c2642d6841003a030318440c4c8208000c0040d0313400ea100801607641015070080020249800000e0954010041211910a04801440056094a00a1304040c0c4991205013040301d1940841c2203030840d00051074104013104406401520340d40c440c1354206a9980c24400245c5900d21140c011900050000e004154030410702c11140c41f85140c541c2da001c40f1a502d0401941101030421015030219902c441601d07000503486000b00b08018502102c032402100050807845244001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 715053057 1250 715051807 715051819
    0x3290a05090f0a060b0a06090308030112140607030b011b0b0606030c090a092c032a120409110c030708090a090203040b0402040b090910020c0f03030907030b0705031005 74
    0x504541e030034022100e41c000d8070b0307064810f2120203007030031400380019a40651141c00a4800014401e009410507011242d00a1019086030b2810f0450240c0031028902620184081104a000076030184840e41c40f840f00703901c00085080b644000106444038495a0307105510541000720042040c1000c8a580950308a4040d07561355205544842c85008250b100c4c0c0d00b201100300049500010381d045000900004003556035440d078041c440d0001c841d001c0c0139a040320341041040d00110401c2107401c000d084400001c2c55015901444c2d90340c0b41c005c00305088142d12101080034031144140c0d000d0740b400a01b0721201c0904041c1c0c0c20140644038490b44100030000c6000141080780b03a11000c0801c001008440000c549074506400c010b54886401c4504910071031400d0250301a61601e035040301e00450b0710300020300c40d0310303c91940c540003940b00ca00712a159100c0d035074a402c0758a604000941c0301c2e40000c40a011018558940024110409803081c414001c0c00e000300720034409103002040440d02e044802e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 715054307 1250 715053057 715053061
    0xe060108030913051801090b24010c06240807033c03020708070e0604180b0a020706060902030c09030d1b020105030c0c060c04140301060e010509190c03050103290a05 73
    0xb503178940c03520418100c4180d42800151002d020489510078403c514001c40e0302d8011044044101003200c0c03c5510a01041052180a002c101c2c03c1d8080d40c6a44080d0407404e01080c1000540e825103c01c603803080007141d020003401d0080012900b038200040c140fa0009024070902c40310401d030030f001d10407241040501c0f500b4840301412b100b0010000209000b5090302c0c501a1035000100c480c9004645450003241012005211404210402c5030b110f1341192030805103880d54034009002c4d5003c09000d6441075240c03000030510040d244000e6000b901941d071a15611103a090030700d4281020445e00310140041d400714403469071645410760fa1920f609181c040d1796a5030f400841d410500680c012403103e48220410410007078010b90080c0161071040c0c40900401c111074040500b0f80e0501d00600001581c000010009820030420b0a500030b5145100c00192070000305045045950b160822800251101c00400610400909c000280225903d0040c01d40c0d460007030400f50000301170640d00c621556100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 715055557 1250 715054307 715054321
    0x7030905120a03140c1c0e010905061603060f08070b0d3e130308210f060406090c170403090503030403150e0601180906020d0f0e06010803091305 64
    0x321440150076012101e4440c200003000030020003e034640550180082400b045640c9282c038192400700740d8440100303006101104aa50203020b038122004015922052200300040040c011603104841c8559100150494070f03000609031040d43c1d02410001c45203510030f000b80c50b00815840d0985404950f010303036905001d004400203100203003100140c2030881c40810701d01c44a000d1461a036070845040303400750114800690800b03210707429044510000076001040000d01280141c00c075461032400000310005520300030188920200e4403402070020400408c4140d190904c200703405000c207090704101c408070821018144040102101161122800010307040602c144050000380c0400760540741c41b5940d1b407a0540314681d10100e080c82441c11304001194902e00014003034100c0d071a0781652040003402d00488001449004015246140c082003401807040180c001c2c0c00c1c0380c60008000048407601c50905078242001070b0400040780e0420800ba040c1070f9500d0422020640740e6940009460b11440 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 715056807 1250 715055557 715055563
    0x1903060524070b07080603060709050f090604060314032520031c1106150109030b0705090303191b03050d021b06040b01030c08030304032a020d110103060b090907030905 74
    0x1c2e0005001c0c01d0300208119030298480011070240b00250201c49454440c04000d0346c03132000030b000321504400c0181041d0340d40c0c0b905625460304400081c10000740d44c0d81f13a440d650750200021114003419803000075075503004c40162807013406860166820b19040161543d035006840c40c001c2c810f400d1151b9030040d8841c1684d0502c2030045030010b40002c04841076200e003000e03012041f0209289054000c203000a610034840401b0300191260503907174504030030304550764444104c0010340b405080080502004629840400051801050340000444016540a001803841075140c0f51040c2c15075141405100290304582550a0030071652005038594422641c00c0310f031000343c02540d0380188078080c10304c0700f80141443c54034180e0b8022081c0b160416168050a503807884141d600900140004041c600c1c0c5800841440c2c1010100450850310345010f03400292656480b000b081d143c46002c003403924111b6802d8030607800185070060440f824103522070b0002d0200c54004014109068488001004010042c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 715058057 1250 715056807 715056817
    0xf02030a2f0f1006080307111c0605040323090a060f050c150402031204060c021e1215070c110f0303090a08010506010f0c020f12120406051903060524 66
    0x1c800c6400e403142e410442541d81d40d0184071a4007480c94900007083d26403011048851054002c090003903901c0d051005d11882e1700114102c0c40074950307000b2184000844c5c3e40079a60040d40640c1d605100c666184000800c03928a03140c0766074444200304000d2803242c9480e102c0108842d61410705402c03800c01c4a005455a01c2610f56500e9680580407001226415840501d40201d000f036040342c042d0300c401a090b00040c0b00d640035100100ea00407904000510b02a945118203031607501e000700c00e04082101040e00384503240d60301c041d40d4000c0346601d4030300146200199072242151410b1a400c1010340c8540c41001d40c1300b41c0c070502407403000383c440155845c20011500c00c200c0103480c000495a40300d011900a0030191011800501c00b000d0b41c0c81100e100b98143c0842d0394000b4003911855600d441007181120040c500300b4858012803907595280100c003006072000305456199640c0e101c1e110040c202845500c07140310020b1600e401414441c90b00d8401c02ca0305241251100000e4903101c0c407022200318051 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 715059307 1250 715058057 715058147
    0xd09120f020120060a0c02010603262a0609010614010c1110090303030c14030f06010909020a0f02070b0f0301031203020903070303030c02061e0a0b04090807120f02030a 74
    0x103c014030400c0e40340041d5561203011615410041d492540303200324213945061202620003901d40c20703246070000488130155501c502001d0300c07034035142c5803c0c1c9400c0360048442028a0500d800d050b8841481d0341400039075440b001304c2000708219414882c2c08035001c036500c1c8920781000146c411000802000303200342001103a004040c044640c0c0b101c2c1c0c00404903001740c0002c90002c0d003001c10701c00c0f07010b0081042226100500180c5030030350751480c1c6817072810a0010245410880320980004451342c00740300500d020700207641c0d100548112800043c1c0b41c800d181e171040c80d85e003c2c208100f001401c1480151384c1982c0e4000c1500c0000c04020504502030301034030380b45542c18002d610780041059003650200031481035070b40994410780da4200e004141c90740740b0501441c032405600009000741c3d03415400740110b00001040090100a11785030700e031a13904519401c980c8060641307500d41440d030304001d03200140141c520007146407c60280c03004025090303140614006000c014486640210710400140600ca0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 715060557 1250 715059307 715059347
    0x150a0f020a060e03040302190f140418110a0b070210030e16061e08100302010f1407050313080d090e061519110309010215040f170c0d09120f0201 64
    0xe543d1840341e2294400d1008030300c94074a616400c401c22240003000c0b411121000e90703c100040c81d01c0100b6a2040f0355490700ba510035652132880c0c0400c00b41c080c0f0f20f10301c0350080ca40c403c54494400c00380a1888003030307008184800401d0103400300503a1a041c0384400080c42e0303d4082100d11541803210310301405254540301c1c20031151000300f00141d00082d9018841141507180c1003c07200b40718240d03119541950510440141d42d03809201650050382e6020450805140c111000207240c0c0c00c2c4440e0b034201d2141210301e50030001d12040c0d800451183e100c042e100c00400350407440103504000c0e241c144a48582118007000304d0004e0202e60f1400d03405401e0b061507034801c47d84e5108030040480c420540c003414070049100d141e8403c8c48210f0010507a140c081c010303001080340e540340c4011a038003042e000f4400c84402c03400d01400b00005615070071007441d01c51419040c076282c58184c03a01d14244904000c541041000f2010100701500145039030316585038201807105050b500c14001240d4902c1c0d4100841d82c10a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 715061807 1250 715060557 715060571
    0x30a09020d02030613030801120f03140c010609140f07090e0c28090f05060a030f180503030f01050414040201050a0c020a1d0901050f07080901020d0c030207020f150a0f020a06 77
    0x14007102082907900d40f2980e5040c07d540e80314041620700c00c01d80c005c05400c1800070907102c00020f008200c0d5240c9032014040042c100080c1c00342d407d00391442e9800283c00c254884002002801700f1a8450350441c00c410351503900e0b480d044000a045140910440000c040342d2030100302c245555204542d45c040b041c0141100302e00b07407400c142c0844058111a0400240e00307900006040c2c5500100030700340c070002020285001403c100843c00b90104000282204e595502c0a039801a00c0c00600640070348290302554481c6881c0c40107040251050303000038012070820f03d034030800c3e20102c4032941c0c0c00b82c0c1c24288180c683c899048111307950014020003d4020107192008540f00a08644840b00b000034501020303142e07070310b9881c22400da804c1560f1a20409005101013191035025200b91903014621400042c05d001c00943c010003694140c543c16000300e6800500e040940c140380f075516402c500c0c03e448441495488040341151441000307903010411080401e420b041a101f8801e40c4409500010300b88241 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 715063057 1250 715061807 715061821
    0x1e051801060824040231081e010e061e010f0f03030318060e01020c0c1c0f02062101150c02030703020112060b07061d0d09030305030c0714060103050d1103030a09020d020306 76
    0x140540080070068007901e441a01d80d1b000352101040c203460141000c0c0800e0031140602c3c50245240066918a03552100d5940d81c5103c1c040089911466030350781000710100c2000c8003520361039411303008a9070a01c050300d410321002d103036400f1250171203605140002c1d814420850104110300300042c01440c0600b080b45a801c060415006000b0302c03903455040d11520300103001000002480b41c4000d040c011071040c130b40c1020420a00c0b10001d6540082e02c804e144c00c20741020310f0400d1449400500c2030303c0b18400107021b410b4035541e6684c0d4044460610380039104c405d4001a6452006100090402400c0035554101c045103810501c0280303900f5240d251030b8000c1d8604140a003280a100e11a034505160061209580000e80c04881000e5034883c1c1411a0550701d045441c2e038002002407450190403c02d4800051140e030402104144240251005504600e001d90400c0300320f0300f42500b0405c00804803950070801104170780c0c21207002040021000c12a2004c2240b194640b00302a50600440080101c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 715064307 1250 715063057 715063087
    0x50403120605030d0905100507080307080702150702031e090d0f1b030206040e0a0902060301140102161a0d0b030105090303070305060a12060f061e0518010608240402 73
    0x51441030a401d1100c180c07078505140d9210800394001d400074407045010000c1e401d08002c01c40c120380003403803c10f1400d600354450310351680c0103035000d10004402e039003005800e0b42c3c140011208002500c09154a500f88040000d640c0c0c09261340d12441405107205c20030540c602d19080711005400902200d211047d10305000c0010300551100380c540d02d65103001c1c1c483c0311441450010541c1d50061000341428100100d00069810042108025555504003103000d0380d01e0705c001e18001c3c006c0c2c0103450060820341000a08211300f80700340c110030301b1190f00c00f40500300711009460765000c0640c0ca016221038004c010300d4050101d8941e181d8140d480c0000348150010084003c502c5040291400d2040d070f1a01c50500c40c9907415840340e400111311501980d000200107400c529844a5190800b00d40d99890b05094a2003002074540284280034400b0304104504000c102c8c0110004080041c2c051036140641c09010381900400300e007210704805251502410200c01001d90300c1c1c101800071900d80e00c9c40d4004501e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 715065557 1250 715064307 715064327
    0x2010e06130b010801020a020304060813021306090b090601090501110c060a020c09070f1205040809030d02071d150f0607060c030501061101090302101e050408030f0907030503040b1309050403 84
    0x604641c00c0b400100c2c5070b0605000300c03010b480310744d4011450240741880c2255807500291400c8080240c184210300542c1d504808081d01610311800043c00305d1a0014a40403907102801c0c503401114803108000c441c0c0e1304080c0f80c1d0121134083c00c0c00c106066040085500f40441d801c0740301d0b8442c0000c544000d42030750000d00e03107600702000d0f02d24030700c0360b00e452405882c81e82240d5013490015010400401d207002850708003a80080c4103141da24204458400024240314036a4000310047e4040e18040042420b0303e0740f42001c14012004158090402c1e000c040340d6070100c1030070140601c0c1c40c1d000038211070b02c441049500d0144c02180402072031506e40d40003006454203200c1d2000103000c4c0c028522001606204840503943d0640003813180c0c0c1050304200d00980384500c0c80300e0a134214503501a090180b2400703014807a0380b00340300300d5039030346004076a104a0f940d0184c11b10310340d940041000c1c07000550010072142a01c02882c0340720740310b0148920074200c0020307641001c08500c2c1414141f0082540140740c5407 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 715066807 1250 715065557 715065563
    0x50904051906080f03191b0f0b01050a0b030a1a060c0106050a0b0a02030315040f0f090c0801050915040618050d030f1116050c030d0522050d03030c02010e0613 70
    0x202c4401d030744410842c1c2d6011428000c90135608100141c440400c3d07040300c6d080e0490300c107090207110f510501c0d2000d6001004000240c81d80951031942c0d004111200c000140500f0701140c12078481c504080301002940001002d0307801c200c2e504c401c40703c0740c1c940e0b104400301c02107002041160b41e1407202d94003a02038680303803189a00501c0e00c007001040c0c141140f019120400c05c203500a60840c1c1d240000041d5000d03a0f110b0311500700748e5600490550201c980607210f030300781e8085000701d6103c4032460102900305040e0302410300c1ea45440180851204040b8200b4454401500000c0c03007a1114108000102080070305e6400f100303140d88140041000200340c10540b80c11f07549080204140342840403050f03403107000310031010b000200000b4000644501110389038900500842e4440400440403e190a860901500100da40440c412000c1074815200c0d056450076030710703d0640c4500d058007040015040074401001c0c180c84600e083c144034030035440511003040b804121000d9080000d100005210389034025 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 715068057 1250 715066807 715066811
    0x2161b050a1502010506370e090d14070f12050c0303070c050c010207050a06050a12020310030210050f1c020c12220f03230307050d030f0b0f040c0509040519 69
    0x10b119150881c61501c400b1f4000084d40e01c8452014549440645140300c4d00c010b030b5856403404182c0e80c030040420f92003100303680c008040e4005041c0d00a8251003018100ca80c00c2c00d400c02164000840f0154400b408950040b145003a50034041401d44003400340300ca4000c028800441080304a40d4403000c2401400d0094098031544865000126120103071070043d16002010100c003084801e10401c028500c1c4101803030305000070796007a0304040c140d03070003560034810350503a01e034042c02985840c0a0610308c13a2650b0914a08d0502c14020720324050240b0320300090307201e5407440d1080403040b2a0b0100d54004100f142507a4441542110540554021504600244030803204242c0c4010840d0909400c0c0c601e201e54001c0c01601e03541d140e01400004000316801d0b014200090480ca5400304050940c140c8140081c001510001c20001c2c121840b00e0720080e4142d0400018074001d4640f5039800e40440030503200404c11039841c5000380c172648100c40350207411514280c10044541041a88004411403854003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 715069307 1250 715068057 715068061
    0x204090c0302030907170f0321060303070b0115170a0f0f2003070e0901080601050102011b20190b10090507053106030212070302161b050a15020105 65
    0x304500301e00084a0b000d81c0d03a031001c14280041c1d00424000d1640f12018412507000f03800030350340c0f203040d500b00e1250421540c3c400c800880202c500160b0161340301c8001d41c021810540140c482950f600e0042c46130b00c9601c003071003035031202003440f50b443d0501000c800c003203000480c18010f030320000030310300a10003407602071800960f550030700c00a0180f58407101c80340290b800340c1180100b0748195540013904400034001000c1c031044994943d030301782c64001d1117200302401e40c2c0e47c500710019007034800d1100c081140c580140132038441c4d00c3d0007102170300c4031032001a40194004900c0000d130340340c40760000d442d00034060045210000c0000c00c0c0c2e103840c400c080c0709501c04142a65040400241d49080c0c50684c082a01070000c0c1c01080c181c4000c1240c4158110b0681d5104030b00d040d040c2c1000311003a0809130010341c00151500101c401c058140748c0005580c0703011031810483e8820900040c1692030003c024250408a0401340005c441c200000351100400d0280040e0341d0b52400300407203281e009a00055400c0c640 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 715070557 1250 715069307 715069331
    0xb01170c03031e09211c0203030f0c030a060902040f0513090803040206070f060f0b0405070e0f10030615031b050f09130f0e011d03040b07081b010c03020409 69
    0x8199100360668070245060b05103c842603d10582081000b590442003824041480008240f41d1303658200e203141c050301d10810f0510780a43c52980c1c80c4034a400b5540704105001d4604481d803559580700709149011a00c0303031107003c801c0000e0305071607011244038ad0011401082c14006040102e045400480d0301005034140714402205607900854054031300d0070280000783c0541001c0d002800c14521644503608445520340e2004200e07143ca021201e04180d840f40e200089013014460660010f10a06120b190710307000d030b0002040540041240b6004003040a1030300c0403540607400032400f030003004400c100d0620114000900a00c020000d07a403030b03c24144030103103c850141048400e035000c0121314604e04440c4409002c0c501c42c00d54036200d0f20a959410141000802c3d204e40152021610000b00e0403021175030302411403000c160010202504104400c01c180d0208004440800d648201c0c01c688039541d28000384480c080080b4050700d50750a03c1c1265a00c0d030740c550700400543c1d0441c0410008121010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 715071807 1250 715070557 715070563
    0x5010807060c0503040509090f0708030306151801122903060c1e0f121806070908030315030a0f030908100506030a0303091b0b0c0f0f1506010c0b01170c03 68
    0xc2000e040761304108002d00c40c0b42085003001c0c3d8002911401c54510320744207040146081c41c07581c44a00c0c0d03a00040309100c024604800e6500035001c0c5046001c2c10510070704000c070380c051b81246840b0305100c0c2c2141c01d28840c1c106034100356040e2201050300b1501444882c150800740382d00140c0c0c640301e4002e20340007813041c50003039081e1220308100510061150041042c01c030b103180d00a804a0744400c50500c85145126210005548510741203910000c0303201c0410b14082c6030020280456080c40b4400c107003400800d10010a0f80e81c003410820145450351042004a403c0600200c0058a04031200700900c09143c2c202141c001280c0c4000f08441c0c2801e00b1522210848506a44071070b07058004514040101e07109030030500c0841d0068200381c89040039001111245c0c0d509034000e940b0340c0c1002c546030400c00000d00002600b8684040900030b12409840f9464603440c2000d650541900c504000c42c00070392042d07070106829503000405910300d503190014075181c030807419201c032810701c44c144076400c6031300b004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 715073057 1250 715071807 715071827
    0xf1b03030c060f1308030106020d032a0c210f0801081b0d03031e0e121602060c0c1305041b0f0b220905010e0a150905220302010501080706 61
    0x11a0140ca0035440f504452a0000030140940500d4180401200702040c5450000c5000300b015400428041c56008006015151168910301c035030700840c0302080c0c0c0f403440c400741c5481480031071074500c90300301036858142084050071030303902101361006072070041d450703003000a100c12035000d40c90708903260303a803031202070381c1c0e001d41402034070341a102d107c20340c551070520f42c130303280f460078480d00740820f81c40c4084600c40103500508180c00801c2e034980c14030043c80074082c01604604062400210328042c240c4442528000b61028001e0044800041445e41c4032002d1040c01e42b103060040a5218442c440700450014000c25901607032000044001d03c0308692080c030110301242e00404c00c03800c4840c900703104541a600010f034568085114883c1c16007050306401411805451141c00c005001d50500c680340803030003001407400300120300d8a900c0701c0c090110005e40d0012926040404100e5603074a20705118040480c4590f42c1c141450180078008254040d00214107803a0120f0407500460703601c640031500f00110b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 715074307 1250 715073057 715073077
    0xe130207050a0f14060c030a0c03150b070804030c27200a0c14030307030b06071e020a090e150a1406040902030708030309030a03060b0408030a0806120f1b0303 70
    0xc42c005000001e11042c1102030781134050400c40c01d21034900020981000000c590b1032000b010000b04100303c5141034071030f0b403079440d80300c0c6000c011601d0b504010060710080e03806051510396011880d0801c02103014112030240d1392060042910a60340c0d141c101110031030844040046095001034180b1040f10710407600c4d401d001d80392809207221280700208a0f907110216001c10000d10202d00070120385900300d01c01802680030004c5607a0710302408018110341d00b0038490351140341e08204040100d00c0001481034a01401078449074041c0c0148001071603018260700680c1c1003410140e103d46803403404204c14540d007201006200ba45ea0310040404221512041480c04071003060002c01c5d103c2c103090307004c1000c091016003103402c0603445412503459900100c4201509500010f60341e194183d041c05010001c182d03070114582460b04007500103490340150a1140e0801036284002a0701e41c0c1c03503911080e00c10855809880143c07091914032500da015181e80c862071f0741804408044a0300700081203903c40d01c4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 715075557 1250 715074307 715074313
    0x1021b0f2107021201060b0c03030610031e0203070203041a0c0c06210a0216080307021605100e030a06110c15091c180909020f0904030203030a0c1107060e13020705 72
    0x4a20340c200403e41c401c4c00b0078803a0541d03a0f01400f00306015020020020405071800654076480c140007045003618156021504041c10a0214540c001540740480c9800c00800380c0036842e0343d202c0304101d2650241e98407005000140c000c0d00c0d96001664001803030030000442c1501c0c0401d50100c144511489030320440c1a2003000a40380302c00d0003207a00c1440c0d41000710304101501c0d0800411000e100320b4039460003640c0e4104d002052251494042042009022008500305040c07407904000940401980d256501407003400703020080559001d001441e80c00c1d900107010407a07500d03510582c100541045002131500d12924882c440d0744043c1d01c40302d5204086000040801c02180c080ea0030060038030002c80010300c0312610004205502000c003441c043c1809802c0003c00c0956401000404010b07152202e01901c154030038403001c20b40c00b00c11240e119200e40c0c008501800c41d83c804442072040207141c07102070f000c4c1e0313140451ba141d032000d102a0ac184080b90050408203000b07145404030722804100a0182e4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 715076807 1250 715075557 715075567
    0x130605071a090d12110d06170705090a0c021507030615030203091b06040f03050c040b0d11011404050d0b01060807140702040906020c010c021c0e0102061801021b0f21 73
    0x140c403891102503c407844d001d010445990101c0d10355210f4018107080401691142c60502c150581840c1d044142e02c88040201a10b602d002c2c0412402c01e0058900c08182d511a40c44c0c2c2c3c95075008005030160700ca580d60001d661480e10110040c010711560190101104402c1d00d001d100ca40300c1e000341c900a800c0440681613501081300c070314007044060308090381c220905010002c0c4d01d0381c0720740c0749000171400780026144820b40c650030002100e01e90000740b8400d50321890304901082e05d1004001c248070702030a03c01d47c0c046d62141020003e02030343c0c1c0041c0d4805003483c4203008208294022504880c807545032003e080e26401e400380c401540856460380903400038800c0d140580f8050304045841800f518006280440500e0a5400d65145c0e010440160340181c080102178044982d03075925882c818036107142107a0f05a40000d40321080940106004105c3c21000071510000390304a444442c1d0381907540c00e03100e000215142d100c0351005180101800346005182414500d50101a44078803541c011510782 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 715078057 1250 715076807 715076833
    0xa030e01180804090f150305070503122701120903020c0411040e0a020d090c06020309242d0301080a0b0f04032a06051e090a0206091302130605071a09 66
    0xc5c502c4164a10031344e80c039904000c01d002c0c10070b10001c01460241018003407541c2000113040c50059400381c0b0310200e102c1081494082c08410030310b0707060700c1c058200c44460100c4540c01210700152013148960101c0c545600c01d41016000a503143c95280280d50510407400101540d0f0340f02d0050b0b10274440090407550001c1c0300c030b05441d80105940ca00c14100041c820443c0d0711180800d102ea504034a0240c0e2001900200310300c2c080700c40a840b020b2558034a04211449008001c243c002c21340d20b13114440b411990020b0101341c00c00382c640180300b0203150075125a99204840d940b02c08480c41903402081c80ca010070b00703c00d015019280b044d03805403100b1340091540d030f02a1089055200c3c0c411021203500103030100040d02c50181d42d00038054540e45007542908810681c0960f071002e4105492588450a44401a11004280c03035202c101203030291440104401280c020744101c10100b15415034603040802e2442d00030010b000c81074080c40c3d00c094081a541c40050b24068251201c50071640519000c00d04 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 715079307 1250 715078057 715078061
    0x103030804121b0b0f131104090302010603020409081b0a050d0f1b0c061b0b0106180e090105010314010207031d0406081209031c0503150f060a030e0118080409 70
    0x700d50a2032420162001c03c03911142c180307aa0542084030b00103072520a000d00880342100040c0c008640c1d4070581030104490340d0f5103200703800001000307000c2c4e5199040c46041c94000c1d44018000c580180c01403003030420750310b40000c1550210042d1005400103030a40c1008003400601c0305e0000354044010f10b03510848210a9400d000c917090310030200700180408a1140078444070002400c0d1140c045031100c0c50800d20040c15039075180d00c030704002e1018152044045000200141d0454406050050121866440c00f5102c01c00d9030308840c8045400405004c64818158890b904a80c00341821120ba080c014440070b00740e220340000640000e94101d13441c10071081002c6411600d60340104002045a0790304111030801e210342c0034a4003000d601045425082c01d09001340780d484e1074840e05080b02903442c400094030f41d01015110280110007805841e0710307034882c803080801c10341d00100103a4442c038003010014080e000e007141802055007019212400d501c400c40c516010b0a51000129082c91304100503800 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 715080557 1250 715079307 715079333
    0x3080402040f1d1509030f1209010603080a0e0f0108060f0411160501090b0f070801090b0105041d040c14030a0b060a09050117010c140406030b01020f030f0705070b030103030804 78
    0x200c86507550903800b440c0100328410b00986403c1c40041c09280520741451000c521006211810a810801c1202100d01aa8003207541d900390502c0d00c02c0031501c80410641c01014203400c002c1c1030b0400080c1d40e03401160041c0d00c0c044401011501800800700010044809a02c150b550903004001031382180b080d442c01ea00310b043c9000e880001c05042503803c4c1c0d513515504100540079140c9954620311001841030f440c0c4000d620000e40600d01100741400440100950014494a0306441d13030b41c10240d1040e13110b90200c07801002c421384100c0c01124812418404034506031000c071100b10810000040c4000c0e405121841c120f802000b80080280c2134036040746c080c00051101f90301c04150100800c1c19840c500c2201e0181201d00d204004d40d1803074022140c00c451400300301c0c00c20302c885d2000c0f00d07400c1001394040b80c003030755064030700403402074010340044c1e25020142c0e0a04a4900012406410001120000e0507080d03000d04103c407020790f076424004031144000c1c00082d00080c40640082c010580e0f18038007035 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 715081807 1250 715080557 715080581
    0x150304060b04050a09110d0201080708071202181f090b16060606030e0f030408060114040219050a090b0c060c030c280809011b03050a150b071e0308040204 68
    0x206120701c040002400300e84044480075081c83c3d5564113081405001150381614000540780c3d18400415500064492180240782504000051000030401881075050403804060107d065458403e1307103400c3c80426010300b2070365002d4901301684000c0d0064034421300d100c81000e5210b45880c50304101070341000364006561042900540c4c2c0c0c11100040c000d210b120020700c200d5a0000718401030383c0c0e006040640380807049405504c2404148041c000114070a411038601968045584c050300c1d002c100070780584a80d2031035052580b2a0b8110b007680041c000d2120755029501d0546041e11160500144d004141c80400c00d0360002001030000780d002d40003550040622001e05090800c0001e89016006c652800c1c0109a0811903c09030910b4200c0074141d0000f0080740240240000000038416069030140e001c010503403100003144118402c1c0c1d115201c0c611444100d660002c0c2c075000a003405e40d00450048031303102c0615800002d911240c002d4488081da0581c0c401c1d0b29504c40d9020880900b034400140 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 715083057 1250 715081807 715081811
    0xf0507021e0a120b0601140c1504020103110310050118030b01150e030f0a2127170601150f09030807080918060a080f0d031805031209060901060515030406 68
    0x12484040c008411020f480c840c0034800001d280c880c000400540c4203c018a24020052000d84140c90021600502220a00d10100d401d5a00c60004130040c0a004503000c0d140390000051200080c402c260b1182580d400b038954034014244d0407010046040f0501c03001d82940900001442541210f440c902028445490200050f15a040000703040c0313850f1050303055803070344400544000c200c1d80c070165940780c4130f825101610105050754098601540034515051828590503a01349801ca580705220152200c01802040880c1c3e16165a940c0c40c1c00f80610540200000c1c03c8039500d0b8800c41c074102e007410056491f0181e0f10701d5540c82c448907070400c6900310f40c80705082c81500d541e030700d4007070a41210844d0b051043c100340c20280c06000310900d494000000742d821841070384030070420000e500d07a44000f0f03520740081c0344038400290903862010004000c20500000440842405060040c540200c01440c1541c41da5203d00c902a4220f50103441503039040444203003184d00c8200180050340d4894096140 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 715084307 1250 715083057 715083059
    0x620090f150f12010807060e101710030b0c0a020706080414030a0504150822050a05070603020a12060807171903020d0905091504020a020304091505010f0507021e0a 72
    0x1040e445411040c1c20602c180804102d41c991804a40c110303600605004000d480b04904180c002800c0300c1008401e80c0c061007002103200c80d440d218404e0004a00603885068102d400c150520340c030101e0345480107840080d072200c04240130b03024050846000c501d1980042051900d030500030b850a4400800940700c607107801d5504081024180000c05a038425540c6203940e460070102d007081402c44400a41041110010401c04400e90314010201102480410b409010815180c868503201e0078240013003c0340030f05900000c41c20b400d60081c0014642c05d44850300402800383c0a2404c483d00d1b0700c500c80b142e9109c2c070410002e0f003025108003a400c0f4080b2050701c03060006801c0f010701f0424420400c5005a00c201c0e046014035a001d9020005410f04403000c0b40903090031030070340c0c0760141d8030690700388030715800110300e008903008001f04c8008058408042c060080224058104089036114442c04108038000050a0701e210300d04036070300c1e5940244601d1000a0008040d00300109a00c0c40940103441084 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 715085557 1250 715084307 715084339
    0x3070e1207080d0807031506050903210403111012090201110a030f0305090d020c1201090506041a070e0d0b0406060b0f07050d020a24060b04120620090f 67
    0x444403016255070300c0200181030070710300f00402c20140107010f84101480c2c0344040702803032400c120b0402140c4103403412076260711114000a081c04600400740740c4001e60105403420541401c405401128010488035070001c00d0728081c4005840702000500000304404d60311440d40704654418204c0c0350040c035046060124030104c0b9171520f00c404100f50701041903120300c90f803c0c95150103a5540080510050080c0c000a6017010b5660721080d4049881005942a140d10010096005038000390708101150700c0f5040904040c00858000c41c9501c400c11140740010b4200c50107a4860300b0f0140001d42405501c40702510348289020340035008596840d140c0d01c2c001030309220640500144008015441e0350381009140c458505012280141e055410048180012400490302c0781852240845c0304940203045040c4500100507503040002d1181021030080f0361103203106020140b95100e00020004900c0455a06a000155003180710030307140200705500442c100403580d6601282c0c090600081401a07107 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 715086807 1250 715085557 715085563
    0x100b0d060f0f09061a0a2612030c0d0e070f412e080a200a12140a2d09021c0210051818090c01050f03070e12 48
    0x10420340c4d125840d014406031711120004c01c0f03a401502100c91440b00b07440c200c1c042032450041c401000028070b803250074184545040c8030300780308c0c48050104555a86400c203c82200d91f04102c81e0a1150381c0740c1400d8040280d00091040240d4514100baa4040303454203549110711280a09140c0c500c4800042e03c0c0040c4181d0841e00c0040703004100120340e0700b0a800d0500c240780b10341044800942513a0320400039514400820111202c08600d0b0002184d500d07546d84402074052601075684900d00e000c017202d4082d40010260440d04041c0e510707038134a410408480404c0e2002c514403184004c22405c041644140302e03511140e9200b80d00344104121060400b80c4044201c2e100745084502c507102c0007060304518150840b001100b00c00f14140c0300c03141039500450000f408550381b000500c0b80005d01d06d800860031401c14005107000030410350210030030035462460202e040d201030456105265001d0f20942c050020b0f50764020019218a003180e41c1c2c0e040803122140a200c4203074010b01c1e4034501000060040c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 715088057 1250 715086807 715086821
    0xf0b12151807030b040902150a0512130308151e030a021306080f071823100303020d030e0c060a05070b13020a09110304060902210f100b0d060f0f 64
    0x1d512494041c0ca0310300d10240558080280b114400d5280006150050f40d07002e821040154103c1c50594a50661311000e40302407243d418441a00b000d44010040580100c0700729106039403080c0c0e07424000d40c0310304a602c0560402c1d00b96095219245501c4411b4143c01e01c1048080294018111900c2078960f030041172050103c0058034620710345a80b402c0c84000410842002c0f0058130078000c0c100b140ca89000032000824583d0902c103c140c856850700749040b010511810084010030311440075080584140207a070b84140300031005401a0281814054024410746895800740805032010083e5081041095846186e040b000d0100501c034404c00b10344800e41040c801c0983c4514010840e4680c0100001c210f45984091a05030402d14500c58051801c002c4c3c0b0f0b0416840710011894010b14800035009a40b402c51108010031152035844103058000b0b103180000400c2002d40700c01403c07013400c04050300c2c00d100c031980d0403809202901001650b1940030050b4541c2e07642c8009402001100400103a8140c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 715089307 1250 715088057 715088089
    0x60e100c2a0603061a070206070b060d12020a110a060203070813170f01060f0b090915031c091403120309011b0e0112090c120f060504030201150f0b1215 67
    0x140d808244142448174503000a481070444506080104607400100703107105810004024110940202d910f035242c0200a03402c0a9000d021440640c0c04004025901d807030841c0b0590b030f04815003040341e000382000c201010a40d42164045c51a202e03a6882e040919803103403616000480c2c841c000040c0c640c0141c101030301007042130303409090800c8040c95500c1c2500d010b03030480e144d201d028140030491155504100d0f44202c40580d51074079a60f907100038001140d0290103555401d40131700343c070ee0b080d0b0804840c1591580c4044e62030701c294a5880c1e621000303104803a601070300c0d0140d0010242d0005140c012000d907030300010090020600d000003482d20b0207070519058040d40440d0402420250940e0800e188551031000d15208011510300e6072200d100c4c00000740300d03215101e01035011020074004029141e44003241c100c1801d00440c00e01d0f183c024003c149041d003c10081030302d5000410380d6220074030181d044461266061b800c08040545030307a200c1001400440e5481c0395500402110380303407135079684400c0301 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 715090557 1250 715089307 715089311
    0x703030216080102160f02010509100905040e03090303070609020a17030307090608090c13020f04030503030a051b0409051324060906030807060b060c100204060e100c2a0603 76
    0x50149100c1c5800e02542055120b6401030080580c00c400740090a00c481d034022244414490b05800181c40c580301304194941c00041440008a20503082107040048035803c0c1c038100685038840381007585a028401c00560f140d0010440380c070208501d5044a5407240c001410055685e645803d0200032007440d14010125400200403c40115085000d050062900e41402c0320320b40781c440601070300c516007800014460b0810712021511443c2c0f55060b60100d1205109007035860f500c03824081e94a4000302d80c49040c00d4180400101c41c0708015070101031020400040ca824070f030030006104082c1000400144800206060800110303550b18004000d000315810464824400425440103403826134001f001260b040003010000251128206c0c0c912580055000902501e0359000a030075114071182481107120b00901e401058526030300a2040b40c034651548034032071010a06001441d55002c071094042001c2210f8100400d006070985820507444a840c221b4610740610000f02e029069000900080e07 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 715091807 1250 715090557 715090573
    0xf12020f1c060b100f0c0302010e0a0305130501140f09032802330c07031a010f060801030c030b19020a09050a0504151512110d0525140c07030302 64
    0x40541c0c410742d0b040f40c1007510868201030304188040c140d440c2c006000010408009083c000341403003903029040021300d041c2a103183e20481e0400504a800c01a02c801e1450600c041c0003d503036005000b03060251903c2c10303903a801c092205070300340701980128901c283c141c01035051802c401384100d420107001841000300560041c0141c018802d6000603040e002d04552240c0d115000503c0480d00d8417044d401200c01c0c1aaa507262801c0c3d42800c00712250320080201d0b4002d42c0d07440900ba4210440ba040e96020a01000c66076501c80d42143c2d803038000c2c44082d100e119240e1040c00400c2590309615030100e0410406003803140d02100d4039013203a2210400347e0005050b1501805146080707020075004148c215014411520000c0001b06c0c10650f520500360001e2200410701c1d074041c060503003850008403082c000c0046285851405405d9888000104180b0b443c10000035503c120341e400716401103d240341209240110300c00c040d1440303040005201a120404e20800c014003004100710005103100358064140c1c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 715093057 1250 715091807 715091813
    0x5100e071103160f020d03080403020f0c06072a09060f300507171b0d05072706082404032a060c0206070e0102070f12020f1c 55
    0x410809030224040041c01a00140d440d9000801d940040b02d410348451a00361442c98402c1c15810000300003504801e8400e41541031507003002c1c10310300c5180242c00391681c0900b0390400c0e50700c1d07030400429144d22080a004000100d840407070a69489506010301040300819858140d9034000d00d42d100c107190b03546030842440349940e4504844000c00c40c80e20304a420514240c03800c42101048940141514014104007090210410202d07005001078401e42802d4a40003e080b62200e070140803d1020f80d00c0206190b01a00788002e989400982100c05801094100714001d00c0b0440c51941e8800d149403960000d0510312814802c0354003c0040344001c00c0301010304405c900c000130545204e1000c580005040001294100d40c40c07031103100014050349503111001c0c0240b00005402c0303030046d10440c0382040c0203451035000200300340110040d84804601c41440b10049a0700d5103180501181032840d10300410501c1c10301001c3d0f4006610083c80c2480d4440d4080c00309207003401c0540760980c5403c1014030300042c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 715094307 1250 715093057 715093079
    0x4050406150801022104030c201c08030f19110903010501170d080403031b0c020a0b0a0e010c080904111804050705120a09050f0c0310060e0714070203010510 69
    0x42038110000d500b005c15510121815281076050381500e120303103100140805109915030260f0990103181a15503004000400b012036002000c0b26001e801d0910000d280940b400d00b8480f1220b510045c00b5240d6501c600e0101c00d010405014070b000100d4001400f020310301a1301038003078403280c2800300a44420381c0c1402c00d0300352581a840441d4a120808009507815400b081c3e00600368842d003000b80580c2c5452800720001d00d1607038603480003008085090003020783d05c0080050348900031185e4001441d04c40007181190b1188400e00c40210303a101648000d079501410760b0301402401040c406091142032404241581d51080d0b11403101c500c0010702d8040c00d590701084981888040e80c0821441c40c2600015043c0d102c0c01c5012060b1a0309040080c5081010781c001503100c0e944501514519060740c102180c1d180192001c07079100380501d5a070400d8032242c5200702d04c1114101d40c200e05854071042d80580301c1032204005c848044400b00078403409a00e01b4060300d80914103e85a19107441e01d0114000b103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 715095557 1250 715094307 715094309
    0xa0c021002010c17010812210406020406020d030c020304260708032205010219110a0305030406030e15060607020126180109020a1406090924120303190b0405040615 72
    0x1e0184d0701c82005001000b8005104034084481e1003c26684858803000c4210004582d00418a801c100304104010004650054012140385d82c0072035101c980d4501003035042c0c0300000010380050b4818070003007240c803074904014081c0480c000d070307100b1800310414030050a069041e0401001944001a0342d201d00500701ca4210340301c1c0841046800c8a820500000d4480c00081464940550b440040e4070174030406049420918500400e40c4408075640d140c9284c03240c006210303860209281c440000c84081011441c02c9450398840700d0404550790304000c000044e00410400c1e0704100650343c00075000200100581c403c007442d54280721052400b08001d400403d4034400f1401941d05050190006881b107802103410341d50820044184101000b002c11024001e2920207944416800c00744082ca00f02401450001c03190a50305580b0f240318038040c44282d10706040c0c80c04450f8001c02c002002d5640d100142842140c1003d0b000c600c98401c00001802d544080c1d50544091ba41c600c1d05442031303404004480 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 715096807 1250 715095557 715095587
    0x705071b03031803050a030f0e030f0708010b010309051009230f0607090602030a0f140403060203040b01080a0f060b010e0405191415040b060409060e161d060a0c021002010c 76
    0xc41c4141190303265030303e0341c07054030006048c0800b00d144144214000c41808070f1681024044520781140c0c0401145e85120b40d11030000c440d46424072003000e075407203030140744070094000340101805210f581d90f050041100490a40348820500f00380c0a6240a030321000b0082040708009119160390004103d003000720140552003030103260748080204640100a0b81c065011a04001d590800d060b01c0903110120040c80c40c42145000240220421070070b503000e03500550080088054981e240c1d400c403a41c4091000f03000e0f0030070014000c40000964141c020010030743c0b040c036241440c2142a03020a081d1501941d0b00c2c0080d003c0d082d06800c400071144203840e42c0d011a442c2c81380c01410031044500c00ca0418101560180362185007202044d1512400c44d4018240c00404005180c0e480e081041402e01c00d8030f01c0040c4401c8014000b50061059400719000c03114152803030388109280040101c140e0125824005000001e0f42090240e134a04030f149403980f5258002040ea00c0400a008005c01c90302c070404 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 715098057 1250 715096807 715096847
    0xc07080d1e0e0d0212070e0a06050604150c0f03030f0b010e01090501111609021e0703050a0c110901061e08010e01030204200301060c110301020304030c02090705071b0303 75
    0x1403000081441c41c1811401c1560401c0c00c1d60544410120f165004203142c081d401c036804074800c81041d1000220401100c44107102500191943e802d1074003501e196210b090351000041c0003d100b4074051052030100c004103801e00c0c1d09000f110355a41c1003040303030125055011a5850382c556080c201103000c2d40b1502642441c0070b10301c2003207900001e00300b60b01d41d0084038100b09094103004400c00042160883c203615207140c0050340c03a40d406c0c0c5180a544801e8641180ca0f00c003402c04801901900203403250581d15032102410078400e9407007200c1c4640100c0d41501c407030040c0c80600526443e0303403400311b000e04180c0c1e84400c190442c03200b030410b01002c0c508480c0c0821041798010841c20003a240c0c01c1e415030354122008204904400f003608000c41d072081101d06290800030002075482d8000d00340c0f400e00780c45044843d246240260400d0308038001182c01a000c11440c0c411f002c0186801070000750312560f03c6c10320905105040d1180740394001a03912101c0d845081c03c1090043c581c11070780b410602c030a85050703 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 715099307 1250 715098057 715098077
    0x10615110d23030906090c030d05041e03120305151e040c020a0209130c06111e160f09050f010302060d0e0c090f070f08071d04020f0c07080d 62
    0x144558030740704160508104082c8a45110004a800302001c0b441201441800d0b164101008015101c1900f074454810341c0c4142003000c01c0c1410041a02d0910310160380b2010308081c509544142102641c0c58a070105058103140880041c03803819031000c010840340c1e0b00252a240452081803c107505003011031248151087c0306a03139000100d4142c51140040d80d000c2250007400c1000da180c080c2060009501140f40020405e2446802101c110054003501d00030411035500c0b00b0540c1c80600c40346001840340c022022428401d11551a418543c2885408075441406190f6002102980640040c10044240719042100607141d000b10381d0400043e08000095516550000d8254413410712000401900c4126920741c1e10820310400b181b0481c0500701c61172600d8180316891300791804076000d00c0403900031400c20390890b01c503081c5644500c0741c548800069116160181d0090381c0c1c94180c175a0f04c2502040407100c9c9186078000340c2800c0d52583e0080c20064240350748a41805560b5100e0b00c100589104 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 715100557 1250 715099307 715099337
    0x10140f061b0f07230a030c030b070f17041b0e0a0e010e16030b0910051602010c02010603030504170111040f030c0e042018042012070b0c1e010615 64
    0x44c03202d4000048000481a511400020942100035580050702c52400c0b294000180200540035070311418040d6280302c0c010760b050a003503070740041302c0e0400068080141300050000303540200c06552203080c1100c10a07104d07074070041d16a0010044802d042031a48541c1d084240c45001d0003464040084003000c1c0040041c2680710f00700f4040c503440041c03c4051020085640143c0602070380700c080c502d00d0030900c11490030800c0118054a0700c55018010341ca00340041150a1040c410072090301d62681d21145040e150030030b440840022400b60003030039540c1e107181804540c0c0c6007004100405900d07500b40300803461070034280e014800c20b42c003541c44030000c68100400607403e0842801520a0f640705801c1281084001c07540d10304180c804204003e207400e0611040c4414940e40c2c8841500d90001850040004024401f0a0ba22000c17504641c1e03208080074000d107520381d0080c02c010382c0207508854050002070034804299240b10131582c61039640760f106000d400b00091207920080d0740c034201604070000b030301d03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 715101807 1250 715100557 715100579
    0x307150f0c15050403120905030a08010e060d0204050a060f14010212120a200313170f0d05060d170307080106050304020f090703061d0a0b0910140f061b0f07 69
    0x942d00e62540b0758400000b020140500b01d04140703c0441c3e0000c0286549500e81f45551b42c1c4503410443c040341d0384400001e0041180d00940e0f10a010240128298924540c00d1001808024001d0552151520008289051034030319000003414069401d8088180c1103001a080c000d6086110300d020504004101e00038441c82402d03608007500c2c403000034050020354a951070301e080703c1145a448082c00814000c4010045014408a60144400c0360400d14044202031851041c25400f000c012000c2c480204400b40540c03016030b00420181c00ba4441c00056901d035080c0020340c100904c00c0034008000d001c02d203a8010203807030142c422410b00500e5403c20b40c0000d1990440b902101348203460900c009400c403480303a00702900411242035500b0240c0c0042d03603607079026141182d220012602c0d0500070705291400184680c0551004041e200c0160306001e20030780700e500100c1a82e6045003001c00a03603829100c80005003501c50303031190800070303d4907118403481c02c20a00300e8444005900c00e020902514842c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 715103057 1250 715101807 715101833
    0x2060121031719020d0c0207060207060e0f0307080106030f0311060c121906060518030307020a0b0705190f1a1918020301020c01060302100c0c090c020102090307150f0c 74
    0x2140c0b403180a9554101c1c91a4408450032621844500125030f03140c11001a40001440450540030354071501d44591080f640c0700c3c15446800001424070101110906042a00404205000c1c090b103607881d4888040350f0a41e46154811101140301a200030705060b40858070183d00205403018222504000c05e80143e240500701041010510040200c2c1d92884200d40d98402c1c648400c8041c044980c0c0e525001c0c200c1d80058074004114480402d0040c85071401108030350510354000e0140b160380c4e013807e400c85440d400054003102d488c442c54280200829055a18a001030700c92040c8a0303901c4c4040c0f4001c04080345c08008140130800714020702149403003920300c41e541010400d5001600440840e0318007034a40b091100690103520000c0c904482c000b0640001064034000c0e06c2c1590760b911246012100d4600401c00035119180d03a034002d00030300c42c40380c010740f4114101d0b2001500b003203c8040040e060110690244056180c100355014071550403045194600f8401c0c24804140e00d41d503240c5928841b11 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 715104307 1250 715103057 715103087
    0x30f1b030807110c04060e31170c1f0b0d0b06010e03150109090b060a03081c020d0509060105040b120c04051012050309011806021f020c030a0206012103 67
    0x10030710803e048210030002102d60320710080084c041c156860000800c140b000f0744004203d1007014200007844c1108060311401402c4103107006c4540c50240d100c40c01400040b1140c01c2c1c00718002c0045003d034800c2004049030506044c080040c00303a042d43c490764110f0b0b602116442c0610203c50480c80031030450050641c0c44003082c24502c641203841d900203420719aa8109007040215600004101e0241561007084050300c02d00101295444090400c1140e059501c002020007504002011207031844900c3c0015200c5c50800150a140c5080b00c580262001180e1804140d40203038010401403501d8054292001404d9994001c2d04101c00440364840d401da4030128055038444000c580460b08000c44440202504080760140d01da1070b21f001916503229a442d6800034440c0307150100c034801d10740502011604113800070194482e5098580d5000c11600241c02d10702c0b5400e00000d0f1031302c0320038401015510b900798003a01700b540c10f2100800610190101042a01074100408030021380c0281c400480c1d102 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 715105557 1250 715104307 715104317
    0x16030c0813150e010606030905070905010b1605010f020c0c010f0315122d2a171c170f090d3005010305150403020309150f0403030f1b030807 62
    0x108030b100305006408400f10000141d0710301400007621039031640c010b5031542d1040087e60780c01c942e9400ca540c01d546084c081c806080c00d04210145200c0480b00d01552800d120304004034002c0d51a010038022a0000d250f1400746401070b00703e550066a01c180405880319850404100803401040d0301020a0a00c0c01958181c0c05402c00c010140040d902000da10461503080341560141d0000c608000380b01d003030008a40da0040c082d0044640004620200d03d24180c0102d007541041c03802d103030501002182d9031091224000d1502d004441c0030300e0355260382c101c0705540f50303910303048405500e0720030a001c020b1041500f00611424854000c42c04512199004440e280807070204c030008048030b00708030030410151051040c00581d4162002550801070480740204291803454400c140d420300d21001c00c481c001c0c01038108002151040ca0030400315030000074175031052030030b01001010000302c1d030b480b540040d00031802112481048a922074400040560b07001a028407040490354007414081028140c007007400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 715106807 1250 715105557 715105583
    0x190915050405131406010e030c0405040311060f090d0f26071b020a27020408150a141b0c060411030d0c050706030f11030f0702010b01020312060d020102031216030c0813 74
    0x50340270090701c09401e000a000300003d0400e4680a000300c0942d001c41c240a00817038000894202c01014814070030081e040151100b00c2c05108100c0d5450713902e00c1c080007881341c13a0b0049070303040005c00a40364484030b0900310100a421300341d902030804619160304400341c400140084e401a1210415041120106960340c402041d008900b01c3c195180240080c40441c4045000204030340e002801c3e6800e1568420400b10710f44940d0180d8007610080c11005182d0101d103404507a0f400341c60032a400095081ca101075080035090f0b044103042090907501a81d245d10700f44048034140c0740910101c040070700c96003070000a00701036980b615220941c611943c403c0c540ea4080180e490700c0a5003007020200d108856050b40c1c0e161880d00711008980a0f68000015841c1c0b0307904020f00d500000c2182d00b00c5200300034007141b503a5a1002c00107030034217143c8220b045000901040840a60801d0703d0b0340030300d800c04061401a1003132040281141c50200301c4104100384c11062040c403080425440a46c01d8100e814401c501c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 715107913 1106 715106807 715106809
    0x30f0c0c0b0f0402040e010905031215011d0d020d08071106040b04051c050f06040312050c030112060908031e100605190915050405131406010e 63
    0x12001141c04540b0750b014140920f5840342c80100041039000c2c44410031400e407092440b00302c482d684040f40c0404075400c051005548030b070082c09070b1000c424071040000c0c6070b1381b1002070130f00103401143d120240c151038240010381310304d4020303001152070740b418506118203038001d85040d1510b007004505140c46140c0705080f05c0854455204040c06c007030804e8200300c401198038a0f103100c003195031002d541c005071041c00885451070300170014010fa03252506007e442803c1c02d040b151402450071041108045804003628191541c80c410302c43c80402c6850420010075035150040c0c04102c02000308050f825851000301d6581620070007010300d03034940d103088522030a2280100c00124100b884204284060b036458400e030300303205140c0943e10554540380316180c1c0e02e4581c0044000b603000503050003281010141000e41c40340f0540c042280e0041080003464890018002d18100041e4a90002c09 = true := by decide +kernel

theorem cover : BRFrame.Cov 714928057 715107913 := by
  have h0 := BRFrame.cov_init 714928057
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714928057 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 714928057 ≤ n) (h2 : n < 715107913) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
