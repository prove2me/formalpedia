-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2932
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:10:25.162276+00:00
-- url     : https://prove2.me/submissions/5e2e349e-5e89-44ce-a7fb-01d5c7e6b6eb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 527158273 ≤ n < 527338129 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 527159523 1250 527158273 527158319
    0xa0c140c06160507120f0b010909050a030e03100606090806011205100b04020904020c010e0f030c300a0f0f021606050d060e01080c0f150a0f1e0309050c0d0c 69
    0x1419403039a80c071109800c152582660400340b00c1119400704010300110712301400b916041403011040d1682c0c3c003a0354501400c001000d0094100c480ea82c5501c041140c4507074071800d841c05120050f618036018108401602917020305010b141c00109400284401860380250300400402c0580000e002010040031a100c4aa500c40d80802011149542d00d0014040a5155800000e6074104001c44503141030044400b844041c0c0040c0008901c81901046201c00a03100300b500c4209520942d40a40349060040305003c401c40d000304d00902d44580c80403016045445648461031018040c4505a03641d8140b040c03801d0804145906c1405004d100e03a0141800034040c600102d040d903151a81b18008003001d03089000141e01040c201092880c0c03000041c903010000f503c1083c2040008400d0b0446446060316003802c0c0300c6080c1c0c4890800c0d1042401c4000141d69020075040b1171403411008001d01000c44050b04c4603c00e0007070641e083e20700f540c190701c2c900b540407985500c141c0c9000300c2c40d0450340748a03031405c00c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 527160773 1250 527159523 527159533
    0xf0418020d09060b090a0b1c060e01090f021003060e06040b032b030f090506011401020a0c180e0105091c050403050304030b01030215031e04060608030a0c140c061605 73
    0x76240341030103041041c600c91540032510140748411701102c40f00080202c200b150510024a00a4580098a008800090b0f2020000007420f0811101a00c0c0d404601c2049601e82902502802400030a0402c5c1500c07c403040c40c01000044001c90070f481460181001903040078000c521107140030781c080301c01c400f0050291765811440c1d0312076003d9810390b5401345001141d2010141c0b4241e9040c07081c0c2905803a084401c00811906441d4650782e910140103070b85801c1c50b010100c4c2e40302ea00030404800050b500c05a01c0000c107403111800b50020303a06003030811880b820121102082401030191500c00c541e40310040c01c901c10103211100166040844c00c806200d070810020000c15410300c024000741d8000e050454003540345105200d040094506c1c8140118001e1062103481103954145007241d10705140c01141d00d803a01e04000380208849c2e840074039680310020312101002d03040141d0108080c044d001200e41042c002070415216200c1c02d54590340301c001004000007003c211050204950300810407a9 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 527162023 1250 527160773 527160787
    0x6061d09060a0306091b080304060e04050601031803030204030302150106020d080c0d02042d03020d0f06060513050412030c12090c170a06050703150512120f090f060f041802 76
    0x44201c80728017805849001d1501091500c0241c4440c01800509030240214501450700c20024082440d52a580f48941c0d02c802c041501c81c7e100750000c6102c42081d18286002d2034091601030b0096010781700850142c0155840100840703d226a26812a443ca8020f000c6014009004607084900140320426010061001c4030340000a4405000a010a0080380444941203e20203440c2800701400c00c0b0401c840040510050700c2d080340124806501c2041b099814a20303140c80b0300600300c83c0e0403851b08420640d45454040e2101d820140c01180540c00165001308200310490550300e8044050000c24841100e80c031407a1120340c80a281039014008605040e80c40308580360109900f00c1d1424220b0344140415007d01c951441482e400103e00c1c101080306a0340007400307a0031045984502481403102c42e4078a031f0001010b0103082c1d00c009403510788680d03c802d030908410b811303002480f031680186040059040c40b03090035412907081c2d40c4031001e550700b4585000003100343d010a058002c40c035141c0900900c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 527163273 1250 527162023 527162033
    0x1b19080403180807051903051203090309040f050402040b030705060a050a1205090304080d0e0306150d05010c1e020111030402040e070e040c030b0f101e031a07020106061d09060a03 79
    0x2c840584060f40c040c00d4550310b0a000c22440d250b68507400d001c2091411810000030380700048001080c90444242600c1e6030714041101d00318001c400d00e00350403034100100216614965844144224403c40313040103c48003403010316a44140c280a01c0e9041502080500c0c0403d02850103000b10b00150b03c0c09840640c411500c00c0b0a403a0305990f40c80b203039407020034244485c007424031100c40082e8852400c40c06041c5d181c030001c3e94460001e4081d0b08070030000c0b081d02d6540c3d2a00c100c1c0c2038a40390480300910400340c0c040401440c0d40c00e200180c00c81400440c0010520a00c1805a14030301782c20440301b141113444a800f0000104480e0913515840e00c6100000500651001d014920581c000d900e240e004514506260050407002818400007822044c10800003000b030040010035a0082100140e42c00780041d40c4e000b42da1203079000500012a03a0744450b00840840c0840f41c80743d40903034024400180e070340c107007512050550350080ca041c81a80d00c415004c1c1c108180601e9000714001c0c006806e0540e00e07122 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 527164523 1250 527163273 527163317
    0x32d060b0c070e06030a050c01140f03070f0e010f08150316080102180f010c030c031b050705041503020a14040603140105180606150f0f0a081b19080403 67
    0x1000c800da4224600403c01400000c5586604c14400d4000c2c141c014000d6031001d031121803040b003080c14480440e081801d81d030110000d0721080c150141c61240d4a0404c000003510b010400e2019038005807240301030b030515511171009080e1b10070180d20703504120388400c003645410014141d105a0140b0805100303c82e50b40307050300400c0c0182540c03400140e4400d1503071090004034800001c020301803100544618010f90744144035032070160b058034220040802c03910301210040e510b49903042c2840120405c407024001c01240c01421950212070030010300818002000c100b001070f20002e580076603c06420003c403070700030340c4090031000018000221a5160307902c000e81c007400b0140400e05695140100040c070b0300e11100754075000741c65400400c03140c60400d000862040e03000311504031400c1d01040a20800b040c28040c2c0d4488101120700030b41f03a20040c040141019800c840044800c898404030114131100141100e081101103010510481c01d035840c180c0f0030300c201600480c03c100f5001600c91541e522880 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 527165773 1250 527164523 527164537
    0x604090b010e040c08010207020a03080c0f07270e03041e08030324011d010e120d0f1416080a0e040e07170f100e0a06050106050d0c032d060b 62
    0x140d080b024202410b015654003040e400c400b03ea60300c1000000090307600c004403a0700b1294020021591001049a040d00708181020706c2c5085100d07506010501d000c8201c3c1e00e800100802e00817070903c45050400209541e004900744142d83c1040009000d102c44042d45e9400700c5541c102600d050a035204c10091855108858414040b0151040681030b0070700c60f07d180384211800d04c0c00e4400c05130700c1070604411046180b0300034140005a01c040b4646d03100c0620075000954101c0540789006607400300a0040d02035601c01c0350026854841f62240c540c0c100c4161007440b0b140408103c1880c1c6255070b081041d911013028041801100000402c0315a941e004009515581b90041c101040c500000f080701104461144c26441e08120300103682c44034000f074104c0302502c40b10302c0030480300070492040382071844140b00503011504000c00071500c2c9400100500900301400f008008074501c00008074101c0c0d582052032542000d00c48040240c8045c10100310014005c80130000034401e50790798602c081940603034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 527167023 1250 527165773 527165789
    0xa0b03060d0b1006030b030604020a2105070305030a0f08071707030212040c060e0a0501140a17070c0507050109120b0612010e0a02030d050702030303191814060606041503050604090b01 81
    0x1410138418a81c3c03502a00040c24015401030240341000d500050500c0840e0241640003c017000c15086100d03043e4001f0704050781c1000940b00129180c0c10310948a60040c0c108502003880400f4a0102a1284243e18462b8403a50303a80703100c10024240d46021888042c2c03030711003011b8091112070071110792501060f0049115620391319115207080b502401e0101c00022071403189203200c6041015076000000d0760b00800c1484412603550300c0ca144150744400e00000724a00d041da40001700803185802c041000300343c03802002195400c1da9204011540602c403406106014445450240001510301c00001c0d0040700040c40c070f5190f0190341001d00e08641c4840031110095220b810040d05508090001628054052400519100c5582c001c01e650b03110281065226200040d1011100c044c0c0d680b00b4031101d180c0e00c0391940b841c8200d0030182120155800042681c1c021f60021510034a45130701120f00321034419038991844840007900380d004010040030b190f00140c0f1070700002c00254080300242d01800c00a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 527168273 1250 527167023 527167051
    0x9070c14030f0409091713030b0c0a0e06030a060305191a01030c0b0f120c0d05060d1e0c05060310060801120507030807230f011a0a0b03060d0b 63
    0x54144440152103200490030160010002e5022005070001200d068130808a0301103400159882e010001a4001c1000071142d80045a00340c40e50444101d024101c6c3d00408010b00c02c2e03281e0100304030300340c41071146281c04521607804a850900b417034800356600114045000480583da512142e08048012902c9140c1e004200c403900100103004050b8070000904440c01d0034998156500c100c1102c0300d42c01200c0100c00e0104903211455441e00484103026440b1034006024201075410300040e030018208500031314248000910603007000d134100100a90880440380d040070741c4d260901c032030240000082e10080c840180100f256107c9400a42c041c0390401402c107001860480300515441040e0003101c081e00c654024640418030004840c000e030b94020b510036a41da1030524240c00c0c05c1c6042c0b206214011449040b401001d90081280313085048501c0c001d0221140100814040c1244125440c0c0e0142400c6424010001b800005c0c6030700501c0078002c40071f4070f41d00c0d440b5011111400c840307900341c003000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 527169523 1250 527168273 527168297
    0x30f06042405090316080408030d061406070b011a040515070b010807030c0e0721090b0105010e092403060f34140d240b0406080403050313020907 64
    0x4000da51444000074040821507400c140800640b01d1180001c009024200c1e69070420510948800300c40080c0035000480c5ea42e0020360004e28050450761141c0d07c0c0030869902000c549007400011101010780c03050783d02c16103a080080301c8280c059031861640380704001740004070701c0b61030302c110800f14808484940360719001240350101701c808058001070215049800200005140032121406443c9803c0c10750b40e1540d10b111084032a14410090750b81415826034a802584560fa8009501180076003269080f0b0381e00c900041d40c4030100c601c98160090b6582000a03440c0e142c00c1400c034040b1002c50400e21105403840c0c0001d19024081d500c50111540ca00b00348440f40104041d05071010040c032160286c2c1d0110f050406c441c2c03a900070350758402d0004804980c03180e40d01d60f038111030114030360100410240c500442400304800c480d8610703414500c203003d00800d84449240079901120484d03562964155180d540c121080d070000f03010700c024603491246410042e0b80c1c090b803c034440e0b490350b81c42468130701e1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 527170773 1250 527169523 527169563
    0x60501050a03210c02060f0a030b010504050102031615150602070e06010806101106091518071509030c0b030901050609010303021b012718060b0406080402030f0604 72
    0x40103a00007407045411031410030000340c82d04078104002c0c1070094451148207501c0020f54019a50300c00080d800540040d941c0343e080d03216009805803031095a02000203061504c01910640720314003a1a000da4000d01000050800180c034000c410381c4030b1030031145490280d02c1520305443d40b1803120030a000c121071060000305d504003c1e100c020001c041c8420340c40d00b030044c0042d0410101030481809540181c504e002410301070702e1040500300005040355101c1c58a907070010344400c482035450114591400201d0712032601d4000092200c401000a058403c0c5030081801e040d10140030030070b0034000d02100000c082110741d0b141800034408515204d641e880c00d011001d00712030340244002d00c6241d040c40144042a80051185900240807100039103103035050b80140d510040c5825040140c0c5450b1015040d40c10b403060500048940e6440419480e449109000c000da07150317401484003050b0309100421040c1e1050380d400341c109001070190380c610b07150034045904080b800c03201510103000744920100700305 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 527172023 1250 527170773 527170781
    0x302040519291b0309010f08060a06030e100213051318060b150d09030e03060408031b1b071806060c06020c0106050a08060106031103060306061e0a0e0406 68
    0x1070001501040903400c20008940051800c001103104803014980c01511500c114201c1c0c1c602c4080c0718202007458008200346a403503012000e03450000c0d1110003401c2c000c07400b44440501804008221411290808030105c0050031050004003051107110540500c0c2a41d600c002d00c500300100000503280c030f04040078019404921000707606920700c0c210190806003d1205020100c99100001003031641c44080010075000080b010041d9022000420900074002980281c010502c01e8860103c0b0900d24030806031505021600501024820070002e990300c0100e20075a03c400c18044002c504201c1030740381e40c1c04682c0d510490101c1540c040c0000f0710101c4d080b2100d0100300341c41400180304580c00e00800400241c59000010b01c101e4000c100280001020741100d07014200c09014910720aa9600405588440c28480d00021901e0040b11010200d0400d003240d1082c0d20150092020b030300c0e28810300040107111040071103080c0c0101029110760b07030f6800201000b03000c0030385040601d0506007404812a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 527173273 1250 527172023 527172049
    0x170a0507030906051c0f060b130504050a0c0804120903080c060a05010801270c09110a120207020f0904031206090c090503060412081503011d010b04050103020f150d02070303020405 79
    0x2004d03051080e0203140c0c00b004c083d40d607000400d07100881c80301c0b0320343c140790054409a00081e201030130204214507441c100c000d05008441d400c64040c0300f00d840d1109000c1c101c1c6c4070454003100041e1540006070208001140e9038441c031000703181080807075980b5180d485a542100030060365540000c018051041a58051540544284c8008001ca0102c0d039058038607011008074040143d4505440c40c400380048106200c0c010282d0040506c000403205600247c2e551041c1904000f10300844603c0360307401034502c01e0b9840554003038003404150000d81e042007000321008000b2401c104a981000140810303501481004000000d00400c1c00901c4510180191044e078220750b0180c1c0c041802c1201090380800e81c5080c4064500b414480c58031217101c00d955800c840380e1000c2c0c0540c24210034880b2101078103074411075102e20f18006c0040c001501c04000175600c0a00c00a54411411840500c05151446040c40b08451000483c1e20300b29128843c4001d03600044015000700340c1c007140c20012410001c00c40044 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 527174523 1250 527173273 527173277
    0xe100815071e0908030a05070201020d090305120f0c01090b1617130c0807030809090c07030e04020d0e011802090121111522050307080613170a0507030906 68
    0x4940761210740240702010740030b001e004403654490b0005060707018803d0a0040c104580c29203643d1080f440c0042c00991000310224014440c0030f410741c5205214540340001e6951020181490b80072a158840e003903008800001c1c020a0100100c440d001401d11407081c80303038846c20442c00946051120400d084451b0305c010020300590895800c1c100c24403c00c020f03440240d8448540100032182810800628150412001407041e504084144000c28020306034a6004032030000860f41e80004415040c040cae4000200440c00451031780e2120700e065005400c03c0c0100e442e0000f1141b4448440c00c1c2903039200c0e0030140031420030402500075800c0184d40e0901405c0303074100481da03141c401c0c0040060700381385400c054a105141003000032a80d40d8040c030009248404400d85490b89892880f501c01d01d100f0b0803251440a407240c6001a0508004c98650308030b900240c0504865541c0548400001141c0b130802c84083e07045d07181065075400c02001400244ca1155a030f07a8503140c040c0341c0588100c2841d00300c581 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 527175773 1250 527174523 527174563
    0x120a05120f0901050c071505180f0304080d0c0f020925080108010b0d0507030305030406090b0c09041a060708030c04030b04200103060b0a0f0e0307060210061e05060a090e1008 77
    0x1b02144145041c811079209045000655a4581840302240da000268408203409401e0018482800002c06031080c2d4040030140c4108100d00101503500014441004059000c0781c0d00850142c68014480c0740e00401019600c40b1121b11011040200c6141e01603003800700300c0c0784005000c0903038240300b044c403140070566080b503515603179441c0c1c1551102c1a100060800400000141c04c05c00103410a4411644c44480c00165080500d04643c20303400804109000d039142c503111a212a12442400490b02e1028001c03529191042d2500042e5500007048203040c41802c00c0000009060b403100d00748a00e0081c4080780c8c00102001c4846400d0105c100054101030a107081884940f00980c200c800100b10342c103281002410340b8900350343c1070920074411a410f0181e40c200140c056000b0030b007103c407075400641c1040240d488086001501030b8203095040c04141d80e0f0018441800d0a90051103d5103181c244446035135501c4203522403004d8101c828040c40415440104101d050402c00402c0003980c01003198 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 527177023 1250 527175773 527175787
    0x15050a14040f030f030309050a0b0103122c0604030507080102070b011409010e04030e280602031602010318050a0303140114010f08060420070b0612120a05120f0901050c 74
    0x940048079501002e13060b00084100001058080d5028030401980310065030852101030030005440c400910050b80c046010550510100d403140303000417808501c69585107005402441200383c40c103007007144181c105c0720410020001c104200243e9008200050001da0b40d1005450003401d010810ba0103800081c905020102c40741c1d440c00b242c0340c1540c0c80b51160b00c0443d80d8070300b02120007880c80583d80d6000131649a2490001400b03400301001c0d00702c00700035a100e0565400049950340f2810f540c010414800010a100561080c1c015040d00002d000c055a1140207684442c0d04228200c0e200302d000c00ea5900d100038103103004845050042540725124995003846c64006400b1411564148003000002c80c002415a9901d0384000154110f005414a20602c4c2c2c103145080b41d40a4030090b80c0d42030303d00000034240d1420280c5015070701e0b41000602041420308000380050340000d540c2100b4008203200d0141d142903d04001c0e480b60072181041511824210156800c40741d001d04110a140010407400c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 527178273 1250 527177023 527177039
    0x190c090c050c250e07020f16050109050f030f072c01030317060a08010207060b0a08061015120e0a060f050c090f030c03241303141315050a1404 63
    0xc5110500700c40f038a8000e850490310303000c042c180c080c0c0020300001c4541c414070402507800200c6006030f240e60400c81d000003c039002038507001030f40ea1044900061846200348264180010030380411200a002ca84161181103503040c2040429001503a01c0000e541a03001c1003c682c0c0d018100c001031660749a00e4550542e140144804040e242481514815801042c0c031a01c88688810003896904004c5440c1c504a20302030000d00f45002c4228800c4041c1c0313801081004011929034000c0a0041e1031060780c0e40390648900131141c508002d0030500002d04c010780c05031139080c0640c4010207001000b42c180d0780700c40d00d00343c4100c6070503105942c000751414040090104241084612103c8103c40c0c02220320750040020745440c81a01419415000d10900b929150841703030050942071241014010303c41d82d80e20340f07413800c4503211a030140000f00e0400d802000c0c04098002445803d1107011107010041d02d9a090490300203081410b032000450002d00ca05c80b99074400740d081c070a011103511803032425144c5003034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 527179523 1250 527178273 527178283
    0x6072c0d050a06020406020c0405060405010f05190801060b04150f02030409110d150503101a010e0409020904052113030222050f0711010e0a1202190c090c050c 70
    0x1414000c0c0388101004081c0201004050001d5500c540190b503101d8503568000d40302c80841004c64003850034640844d610746000d010b114141ea84401940140c81e10700780801c080c031603099800304501d00d032402001c0780c802d8003030048a01901d0800310316669246004000900e001700100c00c1c000300550b0811224126a01004a40460b248000c01060050035100c01c01c41610a00300c81c8524140b84c0b41c0b0020031500341c1c0d0051400c58404409aa0170201c05150301015a0f004096208040c0709616060030158011810140017200c05040081c00001c2a4080303103603041c0695042d100365000046002128001c201c0030a1221046200e89050035000004502502024000240310741d030b10145e580301650b80d940d00c0c0b90103000100c500f0f11503410400d85001142c407064407882c00040c001030004410403c14058068607074508801420f2445041e00d070003548410400d0035000f14019841130031803501345401d4803140719006a015105040c0382c15a02e0b0115404418a403091003000e00c40c6402001000c52 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 527180773 1250 527179523 527179607
    0x20c01020d05090303040e0a090302070605030c070201031508061e090f0a0212160303030204030c090b1c05010e0a0614090609070303030f09080a0e03060711070303050f09060c0607 79
    0x1081070f180d01c03d420000781980195004441c000d000341d020400d10030b401d900824102c031f00036002d46445640b9608100e4051200311004202c0c2d0354200080c1c0c1c0103501c42e40c0801c00f090f069000038085103403285415802c103181540d1801090001e5006000b4868403d01f400d600b01e15000000d007035901828400580340c44520b50f01030f21500c101159249420014040d004120002d5203021a41c81c1e180e18000c0d0003508180000d80d0350a00a0f00082515040b500c070fa00780c042c034001c00c0184040720494030f0715040240e890040b1403c2d502d52184800c080820090040c03000c0c030600340494070310319040c1c01300f5800c200201038030785642c0068213020482102107281401c0e80d13007500e03001c43c0010b01003490f80094030001100074071401000403900d24040e4003810700040004200c050340d4003170325801c0c070440303024042c68280e6032650001482000000d0040c4020900c415422203d1414044041d0016500750417105e110041a0890410004000c2d4011480c01da10915400820b180c054900000010002c0b004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 527182023 1250 527180773 527180777
    0x215010905070926010e10060e070c02100e04020a0924050f21010e07080906070e0f0406050a0b0703120510060f17090c0109080a050613170f030412020c01020d 70
    0xf00c03070004000d8402c1440100d04d0010003e00c0050072040710a9510301c40e2100f4032034894906038001c90f00300b80d00100c5601504860b66440c40c2c0c08078580800c0b01c0001c0310a006c0041c1b002020540c805503c9900243c800f00001c0c2e182d600b2041e141c03000c24101140048d01c0d4000821011908508007501701c0c05444041c4c0d56a46060703115003140c2815501804500c403002d20b81d09031003000045a0505005c480c0c03141081745c1d1000800e4446081c1d80c1d6807032a064030800003140945501e0b07156410b24907101303001303000e0060011501981c1e807008151a41d1064000110303907036001581900307068008030700b0107801807039542c100f20358a424807000401c1e00060140008000b1a10784000e041441000c0400043c6000400716a01c0c1c200705a0300c95440c1022810f0702d0200f007005100180341000071804840f1544c0220240440b90340e080c528851042d02c89004403600010080e0001144865401503c1d250305c1440b80e080d0760703084c1410800d00f0700301d12040c180c0865001c024900701a983c0401d001074840114 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 527183273 1250 527182023 527182049
    0x31703041a13061812050a031404060608061b1602060903010c0207033509011b03030c031104050607021e190509100305030f0307091502150109050709 66
    0x140c0703018299070300c210300c801501021440c240050300808400c03400384144a01e0742004450800d0307021000c3c1440d070b0355010380004400c8002a420034041c4008000413181490b00068800400400c403074000c4099805491540e82d440e130500044108014407508485040b03109200c4501810400d00640b10380240c0461504540288408544904c800d607411030760000c0081c0126541024001d503202600d21042e12080d46064820751104c0c0c004404006a4008034541412500404000c0c00d0035480030055a040040704064440c48440840b1402e2003144a5500403034160408600142520012055803842450410bc1004075603500d000300d424850341918525410195603140c0c607090b1a00304600d42e04102040b000d00000706402e05200150f41c01200c08030540d84482944d458500d03030500008240303034402c000301d80c201c0482001441d40000d080c0b504070003450300d0360710052400c0115000e200140e07202d003c103200804802d81000380500807070401009185801c0702c006000003140d111315000d00e211 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 527184523 1250 527183273 527183281
    0xc0b0405060a140f120609100521070806090d090608100504050712050903121b07140309271807060f1403010e0103020102061e0402130f1b0216031703 66
    0x15000c2500d0011008407499174580f040752582880c5490100e507020b10500151000855000015a0342815101d002d0080c204610b40940340c4000c03200d250300407144501c544003002a124000f003220743d00c160380180141c1010702410324050140c3e011500110140404001004110302c8081c50a1088035001c4801040701d45582c0000d031000030040102d029801e080c4005c009074103400000030909560302c0004000c95603a0242144403000b5101080c0355110020050003000c184c441ca5003541c2c10b0b07141c81c1900e1078200c21400042e1420400d00c0850307040348004141d5540084450310841d07024460341403900e07581e00502ea000b916041325004410500c20351540c4c2c4800789100d903004500043c07815041c1c0744c1d8ad51f10b030124050620024441280188034040000e0441c40a00701103903610b84040c00c0b09030094070740d03071f082050122814527205035440d0345603031003030003002c0501407900d0303002ca903444029401c40112402070502000005124003c14450010400203841142500b050b111090300e4607102c0d22 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 527185773 1250 527184523 527184557
    0x50a02060a0513150e030606060d0e1e06040b0c030613022505030d061d04020f0409020301090f02010810030c050418020306190605150318010e0d08040c0b0405060a 72
    0x10b4030025512810202030046941142071100c1300600302aa1286001c50285078209647c0348002c681290304000103100395036005c04150090407501c080241030b500085450022411802c050b044080c0b190390040c02403105120916405582004840004034910310b4010046025020130340741c034070341c05540001d0f590b5800841055103504806182d40301000c8070002c2c1410790740c07034000c0030b134080c42680f4001002800001340310300c2d00c401f103a809200d07001c0707550740381c0070030039403071886110707181c03c00d40751034a0600595017803094961141c450a154640f4000900004002c10002001990012107521b0300b80040b0f00110b05040448608440210796400c0d010b4101c001038000c1c060007509032080c030303040c0140d000101d440185a4080310b10100500344e520010001103080f1f1084003441402d041022810b0101345e40c6070594190586030008c2803250950314010b240c903039104518000169030318288010052004030302e07001441d0414640381000d003410b001607070070310444840b801801748818100002031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 527187023 1250 527185773 527185777
    0x3030a09410a12060e0c0a121b0506040e07030b100e0d050307080307050a11010c0504090207062702090a050f0705030709031703011401030e03090d021507030e100c050a02060a05 78
    0x45000c810f801c03400003d514088000d4100d034158454580582804251030707042c0030848404072140b00001040c00305903501d0b98134580941c0d100700c60440249045c0403805480c1c080003070008000780c5070840f105241110008007101c112181a6201e290311100c842d12148d8050000020b103102240c2840040c0c4062400915522030060000c128042c0030017006007054106010340390440081d00c0d24403103000c003814007508881b5114034000c04102c01340001d00012185502506c10b02d807044400082e0303903c00014500b4015490310b0541c002c00c290302052011401c1600ca40d0750060201d903410b00003030905010a0080c5c5000034146820018040001014648108080002960041e8520804201d1400c2e505425071003401500040b10140500320b48a5109200c0e800000f1140310140d03050040007000c1060304c400131101603900481590841c070340c240c03264004003200b83c400d450700d15041d0070540c00c0c44462030030300a0303200c2400307115054000416004101a0700d1541c1c110344156580d48000b205031124 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 527188273 1250 527187023 527187029
    0x3050601050f16050a12090b0307081b0d09060204050a1406040920030f010f05030f060106031802040e0a0201091a12070c200328120201020903030a09410a 68
    0x40c4141781d01e00080c4031303107001140f60454142d81d40d1100f4a40750106407980f8801681c990b40040d03041350000f4550300505032200622501c4898107450700101d0341042c8169420310070b0a403802507000a0411151900d64411001451400c052107100542c020009050707008a11a518603151902224100d04d4000038940d0140703404000f08903220305004030103000c80d2500340035141650403459000b142c9841d0000307182d0f0412100b01c006100682c02c00307000b180a030040311640d03a070800d000c00761000180ea0760f004040c801100e4000030309840342a80001441c00c0032030b40c40b800d0710144c1210665441e8034500202c864000941c1090710403500d40795000ca1380f003541000090902d010305480560407c281d51405204004110200c070040c0008100401c013042c003504110b2044004c500200300000c0007029401d0040382180001410480110042410765220524003070014400c9001400800c090a110704502c81240c1c012074000030000380d030388024a840c48440001c1d5076030074007105901d0752207a04050107 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 527189523 1250 527188273 527188283
    0x40e21070f0b010303081302130b0307150806030c010c05120901170103030e18160c021206090607020d020304030309062d030e01143601090f02010e0103050601050f16 73
    0xc0741585050071015210280003c0340010a1440454a030204500590a215070000c0c80385c41280072509001c801002c00c44640b039050700070707110000742c1d041400d0710719000c061349512101141d2a0a804050901070707407003c60340c144040c03484e01c00c021034030002d92001c8640c030301c408040d550b01d43c110044e03a55030307008560221140400d00000c020558441e4940f41c002c00241d615502d40600d0640054800c1c0007201c00325040a0a8030499840c680300c0c0c00740285840c0040d200c6103c5081c441145401d01c04121071100f02580120280a40b03070350b0402001901d01560720140d414181140d40040c4290b441c5d10a2800308070228205000045011070320344180c884542100c4a8030024001c0030b000380c0b070400303030740c00a0b5440e006c00d400503c486024042e104000c0d00c1000b020640d103000101c0659141d480d0307118802c034010f40303806040d15024800e02000078011407400700c4403403e601c00100144110441c090415041c8014071031241d800c44266a00306030714003102900c586440e148031010568000c0c0281ca = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 527190773 1250 527189523 527189543
    0xa080604120c080d06260607050f1309090312061404090501141006090f0806041223040e162c0a0e010521060705070201110d030606030506040e2107 65
    0x68440d2140d41305d070381101e400300460343c1030343c480640541c12a144562034828503080b000002d8600ca215000609030000481181403c00ca0a0300725203649043c42d400000c541aa1041c100c018150003060a15821404840600c611410700a1451740d0845407030a040c0101c0d01c1d0b0a1840c10080290015402c4019411166a152604502c0d08020b1400d038407844001c121030410101d580a4803a48010694001e80300030011382e145ca030703101c100001c0c0c041500c804108805c0219003510686001407401070021005050b181d85c10001b80e88440c00e009030046284010303c0c801c041c0000d4024554401624141c2031044448030703200b5040c4402c0c142807141c4e41c0d0104a107d4040b8880c80c8010b150341c10b80d241030312150180c6565900c003c150314411060400c45501a00000358202e10038070080c850b851043c074201d800f00c0c0c05159220300d8800301201090100c0d445203c28031229070306226065010500b1903052040c44c8607005800d03120f4600e40304003040c90031010001c9011840c01e100705c0b001d29034422701e026 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 527192023 1250 527190773 527190787
    0x207050d02131401150c0201020705090403050705060c070b0703051302150c030d0519050106020318030106090e060711060c041a04080d09080705031b100e030f0f010b0a080604120c08 80
    0x742c0f801024003c2c441034411051035007081170720030380850300110b506130000d010050901040040c44d0a004008030308000c01003002d040060300c1440070500130700c402c000e090745403003080c0360202d10410700802d17030400c15207004200b01442500201e030b2030310150151030048101ea10b090303810a081c0b00f46412070200c0e120004065803105e40c680d00207846210000111030710f41e10010004d00503504288100d138016401402100e002894205144c0100440280000780d0703165284284030582c2d45080000d03c2507000342003001051a044403001480c01c1040c00504401d244c03920010209000d00d00841c4cc03980103510b820303c159040c15048502070400c00d011100030b10f0400800404001c5a4029040940a101800a11404c0002c0c22261304e80620804459503104d500621905261400350b440030041c1014400700c00d51004d00580c03903081e507c48054034540440d00c01d200d0035580f02c21032103409081082010014280c02086440c5c100d0341c404820360464003080d4080301d1166903c0c0001c0e0100340b00059003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 527193273 1250 527192023 527192051
    0x32212210510030510020a080106081306050a05370f1401150917030a0507030509150c07140d080901020a0b01090213080303070c0b060d06021911030a0207050d0213 72
    0x2e4401c681c854003c503120200350070300807410b90041d01404004104202e00502505000c3c0c807140390301082884003100010855100e080135030b601a00c440920556a40a005940300f0780c0006010349910b2000c45544072444078042c5121409100881400603510542140500c801e50080340030407120701e050881031f5071a00c0d800401191100300c9000407802c01d4800152202e501001c040c69a03120001071820305000d00d101742c0e1954060f24003201044010008000b042d43c0760000d0441d48c231f404000c0c140c4c640f9012440b807450300006030018120b0380700715000e0f940160340b0b610448a160381e01000c06c580320542080141c0c0f03001c22001006194104070b80000c580843d4650191845c0402c100c0400c0b002503407401855181c1c03000341c9441c030002c0e0440c0079003404a40607448094120070050407118402c11941c44580407070b08148a03035480f0081c00c10706038003071a500041c2800ca50031940081c5203040a4035001a60300c5109105203401054400449015076460901c03068020003044001d020409030f004031 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 527194523 1250 527193273 527193301
    0x90a020702030a1203240b0a21090c140603010306180c032a06020c0904050712080408010b0102150a0c12020a08040b090705010c080c0c0d05030322122105 68
    0xc4c00e0010380340c0190a12203c240c2114a914580c400c524184402d081102149455012038409801c0c42803120541c0c0c4624202c007180d00d0200d03000c1c0e10000c0c00c10035919140d0110780c19541304060f1055034004c92105550f03010200e0381101d40c0316600041d00c0780c00750890030700c40c810031201821403100190000280062101030903d90344410340c9030b5100109030819404800181d0190f01c0c0185c3c0103031640740c40c1d41060f00000b500280503004586100759100a5a0488001120203c4103a80d010408024682090041000c09403090000d003500208084c0d0000d4620401003410480301c1c0c4621000f840c00340600c42c1514014642c410235543c94800c1000503114072019681110b07450700c010b000855810011441405940c1c05030b6035411100344a4407540c96039008030030350840e00d00422401a4060341c81c1500c40c44c4d800d00c180003640e01c92034441050081909410413a500c070340d00c0d18055000040c4a606c002075a60a80e00708034018201e030161601e0b00302c40d1010040d01d190314003c1800642105840 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 527195773 1250 527194523 527194553
    0x70509070f03060f0e01092c030a0207091109011d090f0609100e160201060b030109060e070203130312020307060f06090b0409051009022e030b031b090a020702030a 72
    0x302030003040e9964680c2c941d4041a4400e00001104000040c0101051f80d0410201120034070440c40e441003480361100c800b940016040407141d072000881801070b0783c042c403203940100080e0b18200700d041b5250b00b90908900c0382005a40c1045941c5e40c04190a08015141802007840580b003030000d8a80400071610400d0240c810320b108415940c001500b80d07050b4401002607540345442041e95459140e110540310ba003001d155401d6540313507140450070fa680c0001940c0284206000450118035240b41c0900080024004804540041101052001c00c540e01e10048079801880b03c4c00d000e0304100120b0640c020510010400c03400c002e1004503900c943c3c1c120b64185d40400034100b002d01c00e100304200860300c0c200710041558221401d000001aa2540281c3c0014005441300404505d160a0f804440310170900c50b40c0340610310050718440036454030417100350100c150700400300e010212800c0545460345004040c4194943e6000885601c80c0d41c064402459000d02207440e0703c03881d031402c0b1030800300b018 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 527197023 1250 527195773 527195777
    0xb0405130203070f1b021206042307050922050a020112090f06050c0403050303040b0f1b0d050603030d09050a05100204030f03030b01031103040b06090f010f0b0c070509070f 76
    0xa20103203280c0054401c581c09101d0303a44500d5140310690b0700c02c2d0b90320a8100181160b0b6000d80300c0c804056124803440412560090010f0402031400d46000d0500c03080d190a4a642409419440c0707011403000290320307003590380460b03801d07031a5541d040c0501c018504002c1e03120015590040f0210400c8800540c0b462254401d803111034030a0715102c400c10480740910300140034940010442400715142e680010340000d010009549403d4403910703582d15680c0705071001c4404114640401441817290180c50340c01c500c5000481000503003818030190a80240c5451840d82541d40c0c01244180d80d04000301c5034496242c0d141480200c8080c02d2a03602c44501c01c45c2070f00c49000c2c62400c054020414801c44091300e41c001d0380e0702c0421000c1c1e1000c8004004401c0c205040c15a6042142c500c0c1c4018406107100c1c9128003060a0b442c81d00c4002e202007044042c001d81d80106200005220b8004043d00300c006440c100d00c3e945441f84400111140751550960181d03400c41c3e0780300140401e55070f00c0f2100c041101019 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 527198273 1250 527197023 527197039
    0x11815050c0c1f150612140601140903010b1f080906070f1103070209041113050c04060e0118030507240c0204110c01050115110c091f0902040b0405 65
    0xc081c01c40024401e400d800c06064010002040e6440308040751040c00020003000010007410000880c0c12039031340754200780d0128460803102c0d81110042c0c06001c03422192401000ca081c10000300192140540301c1c10500311280c0420828400e40f425803040480000003070000c203003050fa5035078440e003010310762030079400190884000501401000a02c6401180b55640d00f8507203000ca208200d51081c10726124030014002005100090b9540f102207501a90140a01e03100d100d1000701002000809144042007003801c0c4810041004400030541d000c55400b03041030004814400012900004503254a2554210200020040c0500080c40205481030184000340303025000194106e0312078041d6a4100140410601c1c00041c24035400900500400080f51414100590090342c00d58009804c500352040e00080025030140c0d00140c1200710384a07001c042c284021b1400081164240000e0080c041d104a946d0241107203010b8a0103e40208031001c021900e0b161911002091940584201e502c99070030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 527199523 1250 527198273 527198281
    0x10050a0f0206010b0f0c100501060228030905060313050f0a05070605040807091e1d0606151e0909010f0e010b04060816030e030f1c050907031401181505 67
    0x90b0a41a41d15080781c40f41814022401400d243d44040b078100310754000c45c0d580762611314160264034007a006580250074411500c3d000440c011410203140b502c2e10030100744000c003081d0010a4103040c1e900c00d4501d15541d030754203500403502c0c594201d030042c6503118036040c0020740302020503007181e420311401c242d850940d60303444101c5840c0168081e039030035900070040405c003072071590340710a0607011002c800f0b41e810800e01d02071204696011400094800304441441d0b08a4010f02613954025011104846001c40e9400d02c00214011020205100303ca812184511401e1060640785040d1000749035511544e1109a80790002100d44110714040c90a1800414864951000d0301c095421954502c2e0886e5207001c818079100c081e18141c0700516965054a01d480242840102850608032a50595621100007840100b1510400c026202072520081c40824a001f141e07180840381c0240c07115840c8010030702220700502c3c08103594103450480900000402602410120300320b02900001c00950b51 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 527200773 1250 527199523 527199527
    0x61505030a1208360705092e0f171005390307050919080616050c0d0306060e09040c05010c1a070e130207020904020d1110050a0f 57
    0x140900040c081c00c0c00c2c40c1c2815800f03102e03094940e8022030354000c04075640c1c0609100300c8050003803048008220381c1c41c489901000805c01c25400103080a886200e450300d04058820101c400780068084615440070302c1307a016140107507101018104000c0e43c0c1d0f5546a84280e01c556580e000e49125549000d0f454509455004a1050740d100340348108206142c1d01c0e04440d42810b003403c3c200010585031041000741f00036550b104c0a584548103546800e5030f204a24410082600c90301110040d42c1c9045034414030001401050841d0450031011442c1d051118481081d1740324059400103004070b204203807006085907403541040d1f0844a1903190200c0000d41c0005104007a0303030440c0c02030b05180d01d1103020045944240702c0640814020111100d4201a50113140e82c03540c0c2c141c1d684400a42402061130b0a4907043c08000450b4038050411854190030b41e0100c4c0111100070b0000c1d00c58020004103d007801020360742008035001c01018241c04518211019100d904007000784400a030001c910f80c2e41e107038 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 527202023 1250 527200773 527200783
    0x6070302030f01050d031110150b070224040b0a050403200a210c080105011716120809030a03121b020c0609010e15070b0c0a08130503090303040306150503 68
    0x90b40311201401d240c0c2808180600d541122104804008103000740c0c40e540c560510400c00030011208010902142e00c0003034510420030751700050f0002004001d19001640c90488488202840440d00d01541e03401c40240700715030040d170340b000410070300000740b90050580c010014401d481c800d4214032211110944007502e03144640c00c0003600700c0b951910030b0013415500e044da5442002012013020307040e00c1315601c40ca200d2005034411115691240014090514545140c40020001200400103144414a4101c0451403071007084102d0800402c11424454240201d9014900c0582124400c81240c81d00800c0904450880a446031600d1250f601480c0042e00c001080c460a034000c155030010401044101d03440001030505100450701244440e40780c07940310011684280e1509a190351071400c20003a400401007000d50394070750802c044003400f80c0001525400002012448001e0529483c1040c503510a00e080e6a40c188804038000007085a03541019818100d01034103001c50650318024181c6d50 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 527203273 1250 527202023 527202031
    0xe0601061b020d0203070504090c0e01150203070308061305190e0c060f220608070e03031207080a0e1e01140603030702090907091404030807093b0c0c0607030203 71
    0x4a01c50a102015207018290f08802c0740c00101605c0100c0ea50b0400181161074801040b91007210084041000c1a81c42001c1401401c0d4850705200c40a084180203440c0c1c4a4154020284182080450580c2c1caaa0610000843c00c1c0c3d2010040c40c00d00702d00c1404901d00c003598038031001d414400b6502c605d000114008021250150096003851800c1c0030201d1141c100c09260040c000b0015800120074030590400c000420242d1034030445820980d100030500100503a6050080d8801c0024000e031103107600d20554040c0076440c05001c0358031181c424101500c1c110462120070320408152104c581d4052610420340e0318250001c00c542408081c4950f10000100c40460b815041030003800f001d410a418644d51242c404410760303075090340301e110071400c6440d95140c1140d01d00400040004040d008843c0580158050070940640c510b0805c2c0c0303d01900d0244903000410600c482481000105000c18100038a0301d407001c04603d18010f1210aa141c115900078605403141601003030300e4600920031203003d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 527204523 1250 527203273 527203307
    0x91e15040e1615020c060d091b1404020d020c0f010c09170606040e03070f03030506040e010219110304170d180b0d150902181002010e031602011407060e060106 70
    0x1152600e0041c403982038043c4003a03000c1d0302034032800002680d1884014060043c05050000d00e101c1c89050007484400c0009001500000400d0203000310704484940b00d0942c20300700e4016940d45540070b1010041d01855075101c03a40c0c40340d4560b12042c0c0e00103401100c0001e08655075002c200b030f0b940e21080c0c861243e00014560542044c3c0114180d402c068010310280a40e00c0c0c1180d01d068403075640c4a000e960006000d800107640c030010703c8601d241030301820200340d000b030000350b0410243c01902d588241106142e2024011002004c00c507049050041e58000c00510b865a503000289629494403001e901d801440050f1001c031520503000c0c040c840c0d070010745c4c1e9603120450800c0d1840c00e40030000d10069801c5e280d00790a10071f00050403441e5000a00c404030f030600c1040c0328400101e09011603001c4a501d40001d59040c25202c8041180000990f5550041d000c160581e005217400180c445407100c0c0000110400000341120612486410041060398000c0455481d6a1390b50000c40741c8601b0705404074030f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 527205773 1250 527204523 527204563
    0x7020109031d06091503190209310c0201061d0f04080d020f0c0f010605060a020d031104030c08060f0a090f03030504050c0402030a0b010801090911091e15040e 70
    0xc0c1c1d14418900b803031034103040500b40b40d2502071040005034044c0d00c0f2401c800100300c4000100990701d03807406c5800303410802490302503042c4034a140c0052180c04d021701c2d40000340382c01c28846248a1401c44000120300752810401c10600b216000000e0281c0000d018081824000f9114984140b42d03014030540714000c40d01200c84591556503604010b40c1c00507a82d44080c917020700244001c00880b000602501c14410014541c444004d1403581c2900c80c150700051160381c06000f900c41560300400c1440031001c452038006548065942d0702001030046d508058020103040d500440d0b58540041c00314054946c903030340c1241720341d140300c16801034074801800140482005d112140000e40a5000700d904140301d503044e1441c00d000f901c0804c041741c1040b41c44d28041038a8400c10440c035608080c40b5409444145010b00c0190801d0b1100442d144114030010700a000050000d002e44c0d01018592000802c604006505400e000080706880c41801181c140f0070ba2509820010801000894004180c0d50107081c0c8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 527207023 1250 527205773 527205797
    0xf08060f040f02130e1e061803040b07060e010c02030406090e010f030206250b0a1113031e0b070305060a060c030806060309011103090708010b090c07080931050702010903 75
    0x80062291140c115151544070600602c5c040e43c14014290750f41d07100a611011899019082e900c0c1003805411480030070105500880d4640c0048200c0701501c820b660580d40e20142131502c5001400e02c1c0030614029460560f000562544c00f000400c03c03034990341d8504d4405a120318100c1d8800e002840340b410580e81c04a400c00042c2400310240000c502e0150b1862495440000410074031545203204461094004080040c07a105501c07500a0300b0328590041400d2801800c0120501021804043d010690003105611192a41400e240c20316910528a40d66400d00310809005401d0588059204016400340465140d00c6208110141601350340c1b11911030b201c6070140181c83d0700c00740592607a552120000d6880261840081d07004228103002007407400e01d0061407900310303424150b00d54800c58824080c0109050b1900c1901c0c0116000b82c041d6980700c540300006044200ca54000c4038004d82900c900c110b655100c401c0900400c4123110042c0702c1c60350f40e500100c1c00c803408845e005011400c510300312 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 527208273 1250 527207023 527207029
    0x1051212220509040c091109010c11030313060c06140c0a14040503120304020f040e0312090c1f03140c0717040306050c030a112110030c0f08060f040f02 67
    0x103220420641d20956594540d0082800154100d070250740c0900300c24000c201c2540a84200120b00500740182ca0411036448002007440c41245000b4080c0a1348130810045070350300b40200c1c1c40c0f420380303c0e540310316295640c03401a042c0d40200f2000d07144585010782d909a980c4003444036604c03030041c40fa9007915103150755800791007017140280c0c00c00940718140004140340e2000c10070510a0312403050410f80382e103090b10412150704420340703015006a041403065880c0c0307180003041e02d48031a030180b000b04503039840009540c5081120f014441d8006151110180c1c0f40101940c40710000006990902640e9052204010807800565800c000718000300444808035040044600d18810490061072030241c1d6512070704240d500c165594441d14a000007400f494441600c00c0e189200110720006040110301c02c0700010b0b100c082c24031451004440c8000844061501c410b12001d19840840003941603160000c0342038410480c00380201e6881482c011031218490034060a209560000644445005603800c1c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 527209523 1250 527208273 527208307
    0x603090b0711070302090a0b041d0601050d060b100906170f07030b01110a0b0108071a03060f03010b090a0623030d05090d1e0b01060c0f061a04060b0301051212 70
    0x149104074083c1a102000580c0c0b4500b001c0c1c05001640c0c4049008081002040110762103002d12111040c0c508c02450350f20f40c000301b0401c0c112482120b2030b202c0c0002c1c3c1c0c100704003d0154980c400d60b000c1d17250324000d0b41756034000e030f40002510300c2e42e611481505034000b07524080403070650f400d4420084840026400c075100782c01c1100d02e0780c4185070140c44450341d10100e80c6171000c0f0b02d50846101070800d005000d007040c00c2004200420200bc1b1560704040c080494150364030010b08124022003079000200e5464070250003081011401a011500f9072500d124801c0050005004100e0080100e44200030703102110030381c103a07038500018080d1000c0000554107850541c450308181e86c02001c003004241c0800d608030480720001e11710303a210000a0b100c07450101c011800c140c0000c0d09100c0705400304c00201d84100f04c02c0d81440d611007000a40b0400c03012304110b0100c00100c2031544107040010101c1c11003501000b440c100c40e01625a40c450100d07003121240c64080c000307883c41d0b07044028000162200b0260321 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 527210773 1250 527209523 527209547
    0xc070e09031c0501081501180f0b1e3102070302010b03030d15090c08133305100b071704050a09020a0f05090a0909060b040501030c06090603090b07 65
    0x81128688025a5070485140740030714448203400d65100010000420301b0b116a003a0143c41c40d112040e03960400801c188201540c5100d4041140d56100d00e4461241c1c5502c02c0804003c0148120401800250240d02003220383e80d006001e20240b00b07210036000c402050303119004150340b20900072007a2001c040c100a4020f202e0540c1150740710400c80300d0644051005101038034250700013140c10b4440e040c0c3e0260709a110390004294234901050800784aa00c003020b03a030003480c03403407140c5404501c83c10302c8110070132440200d4403400c0b640300003140f25910200241d0b824a242e81d01c02d1085565400449400c540c643c4200384070340704c082101c000003404084d03100b00d02c003000c0c0200d030382000e4807140456000003d0340c00c0441503e500165060015800480f100704075091031070244d1904030b002d0003141d03820300326200741c8285548405580c2d08000064000002550000e80100400d43c1d45e070a0406180006105090120310b0640c400f240c49072181c0105d0036800d400c1501c04c1c1941d2101281195a20540d003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 527212023 1250 527210773 527210791
    0x3030b0303070f030c0c0e0601050901050a0e19080c06070f0f050f1515030109080904020708071707120f0804380a0c031505150706020d0914030c070e 66
    0x4102c100150003e41e80c0410b00340a40d95180d1040300790700e481c0365130304002d0b0081e155140440d003c1100c1030380d01c1400c0b074404403020701c3c055450b1085110192540c24065000719400319034001540c0d040701ca03c401c55022a00000c0c00c0350ba01d8039010702402100e01c2010380103001c0d5456045180c01154034035600842640c411011200c040c2c104600700e07410801d9100d0100c24584185003400090103d00030080740d0014100c0007000091000d0f555004140b142c283c8282c0165004910501449040000d442c91203400081c0000501c1110f408032860b540407000441d4207003001141e102c82c4030310441010b4191540390710345540c00c2c0c545032142e4123a40d0201c07107090300b060001c00304045141e03895040081c00c000d0303e010032001410490f080100303070740e100510501010710300a03040c40e43d400310500d02d000b21441a50000710300c803116410b02d4000d114010020381f401d400016840007120444e440b01d400c042c0560000da0344260710a40a9859108020b290603555000003070510a5400b0f03480300541210200b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 527213273 1250 527212023 527212027
    0x91e05070b28030b0d120e090103062f0d0b040f181118150a08151504050408070b070315060e100203120a0e01140411042703030b0303 59
    0x2424034a040d82e0048070103800c14441491261030400c0c400680341c009036007504041c40800421400305030f01c0c0d00003010103043c0d004114030072240e0b14013911804c40320103009404040c003982c503820002c02070800700f40c6207100204003140f2410010861080c030011401c24000e01ca141005894031440900b0880e401d50740c1c029030703071450306d0742c864198031076102c102c00c0402030150680c115050100301404540c3c6032900495804d21143d00b451b040c3e509030f5500a03019405805081c4243c0c1c0480d160844035041410b99110389038030b0a080d0703038040c408180300d0307001c0c40800400650b4070780c00c0c081540c4080e1070081c0800020310010001801c9080c540341e200010b0301e400220a44440122240c2d0720040d400754012810701c0542e800c9a00741031450005c15041ca000644c41c00e88021404452518014407c4c401156240c0004034034003002e402511400c2c16081801c05d25080c41c1c185041d00d81210039170390740315a02e4140700500343d13140c42600550000d00c10b000c05800b80d5950700c060b005002095504c59050000b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 527214523 1250 527213273 527213279
    0x14150709170721020f0a0b0919030807050f0d0e1f02012414040b010206040b1003050304090e0f011407180b070f05060f04020306150111070b0c0c04091e0507 69
    0xb4400c0c5400034040101810b00e00f410500511003e2090312a04c10300802d0495014440c41c008641215140e00302030f5440c826008d0407038134504034001c141c0c1000300010740003d4202305210002611409500003042590810020720070285c443c100700600968001074a48001d80e0040400701203109501c0d031030f00000c1141d100340c591aa0080703090b81103134644582e13901002d11a0f04061034030702070301a10959041119282e03400020b5a02c01c0c000700000c101c2da000b00c001604c49400ca40d0a4001158048100c0f9156904e0301c00d04406031071541414517545c49902000042c000d01400b801300038100040c03440382070707494102040307941d0039a82e15a1000130242590002d41c602d507103401810028010740c2601d25490311490510304265018040c0f485c070000303503c1440090f0b40e020641541020b410800100a007003004010f03104050f40c4001850a4014000005070603032818008014020180c000e031008503031040304203c02c944d48440042c003960141010741c0036134102440a20078140c001c1040300e9065603 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 527215773 1250 527214523 527214539
    0xf030e160303020d14070b010909020a09021303020103050906190c09050d0506100b13050f040e0d020a0b0604020406140a03020c030c010605041103130f021c141507091707 75
    0x3480d9104400580c007200c0d60420f419805001181d5903402d000d44d0718648002c0c2d44414143c9281801000002c80e52a8064400c41d506c0c0a213000c000e00140e1401d41d2600380c070b420650696546448181c0c00f29040c180000da9003040850780324800e4100e802c08041c0c00c0c0711454400000c0046444100074844605404101c43e502c00c044948043e104500601c0307036140c41810390704006e850364890132009005002e101d5582c6205888842900e400f134403070070102c201d96000100a4420b04440c0c081c40e018000d240d14a45a001c5150007065020388010180c6459a40500040744078030311440f00010442886040340d802c25400800451a140c039000d410000381e0b02c01503007154808480740780d140c0e640f444100441e00b001d0148180c00783c450b01441c1d007103180c101e40c1400700101da030303c5c01845907070940c221000710364a052041503031050107032842d050b000083c5002c1e440b40e00c030000014050303c11040702d94138014200030030783d12036645581c2e5040402d143c0b050450540502910000b0715006000011a07058 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 527217023 1250 527215773 527215813
    0x3020f030a0c1812051501050310090812090d02061b1e0702150d05130f020607030c05030c150a05060d2603070e0f03012706090206030c1210060f030e 66
    0xf50703101013520900d240580c0b03820922410105900401c00c0100300c04d59012810540c0c48070505000300b203242c1249031500070f6214040c401200b0035500070510082d1400010341c07103449170481c0c003101d0040c0c5a040311814200c008810001e5203030401c108902062100b0b00e4030448a004040c401c40c1001030690009560144031514408580c43c04982e03040886094044c0c41d400208001c00d09601c84425110500b8001340a0360107402410005803c400300b501c501c52918102d9040010381c1d0320780e0100b001650f1114801207840c4102030940c80454680710b114441c050090000502600c3c03201440d658100d100310800c0b00510f01c44485142504245001030011032154000f60340b0705040d02001001c100220701310041443c01783c3c0c50042c65620481c0d5000110310404208040540c65101c10700c1d00801501081100079003150300031090044030401100a03040702031607101c0040d0f00360b6840300d650910070300b9032042c03a00088194280d0500d0350b0003540180220710415060314003070840302038080402 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 527218273 1250 527217023 527217029
    0x61404021305120a031704080d0e0321010501030b040e1e10090302070f0e0f0601110304030206070c031e0b0c070206070f0b18150c0a1701060c0c0603020f030a0c18 72
    0x143c2120404c0d00c105540240751503074240e42014001124141034546520034000c4c034002404050741c2c2d030700c0300c407410314104281c0c1c02c4044e008800b00f941e00c0f00941c804454800a01c0383e04d012900b06064000300d171030580101d8031441c455034014015074160000c038401c80704030f8001d03000c8036009116031490300150301c0c000c40c80c002c0c2c000c0c0c000307142c000c2c980b1b0b4071280245800d03440700100240d40c1c010700a544d5642c520054002d0000d02c6c0c82008804c2044001d8194821742d80020340c0490001141d1003000340d80c0c0024002c0702c3c020510624a00f40000c075070440030a00410050001d45108009041e0035012005414081d0001d844542004640d6503064440082d01c01d040d50400c550030200316000c80d03101e180014561103103010745103400d40d603140300901e00d03000f8081c0c0c0c141175404079a04003628070078034031170703060080000308068503596411000d80b03041c140318029100c08404810109010f8045d000702e8001c0140f030900286540d41d420340440c002c0000c000003404010b100e50045000381c8090a0b0b0a004e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 527219523 1250 527218273 527218309
    0x2090411030c04180c0f030e1e281a1509011202040b040605030d0509030f070612110306010c08160c06030c1d060307050f220810061404021305 63
    0x60359003000c4c01800030310072400710441c00c1401c08412030303400ca078082811091102103040215405000c02c0d401810400b100201c1d001da64040c0e0118503600c0d00014480601100d4156141e17401e0052300c50303288011081080292541d5440181c40c0690b030034009025502c005c030070a0841c0540e00c2d18000820031042a84280f02d82d20707032441064194503003445001d40c1d213402141d04002080c58000481d86514441c85114140100413032b2041d984d48050000f81c0000300003801381d4108580f6900040c1c1048008002c0090071840c21a031410044201c1044a004071030585a44c0e0b240c0d40c1c19983c0882c150700c6030000420070700c61003a11000107075003000090702500240e20041020400503800911550401c1007800218025800700043c0351141012203401c02604e01d0625030720761885544103080d00c00c01403c0c4040b15209198900c8001200860100340c0b10350105940082210281c0e5105030703070142c080c0d040e0045100054051030b2825234010034151480c8400d190f04c195480000414500051a461038 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 527220773 1250 527219523 527219527
    0x190e0402070609030f090302031018060f0504051606080a090501090c032306010b0a080c040f0308070b0f0603101a03070e0a06080703030516031e020106090c020304140402090411030c 80
    0x10030140c0001e00c17900c103041c83e4505011121315607000a0741d03d00c517407034200308120780c0c404001622400018842c0c1010750010002d0050b040344c410070798010541100c0a40fa51301444452981400708011400110381556941401c40d407517050452009155501301103401c0d6603203000c2c02000603100050304001358010190f141b043d400c072000708288003040d00346190cc0c0341c01c23000062124100e000251040501d20f4501031143d595800c0a4081d18802c0fa003040f60001410718001040065080c01000ba092140300d8450503038481d2502211071724429920180d245d085100c0b4505a10410703404100310006001c24150a00885030102b400c220b8503800c80074242e5550010448400c02034003d88009040d940011f119052031510014642e01400e80d10740340c3c514004564100781882881034246011144400111002849801900a00d9203101d20100d203820301c50f1405130340b800401958115081600401188003c4404000082d84000c51069105545901e03082c112500c1d00301642c401e8860038030071a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 527222023 1250 527220773 527220791
    0x6080c0d0c09090c1403010e060607050a080903190209040f0c0b04090b03012409110417030a02070e010b0a210903090f0b0306060f0a0e0405070203040e1803190e04020706 75
    0x1001380c40b07440880c40c050055820300d481407504804100c03411513000580d583c0c1c00391501c20001c3c18034411918050014410410540180071483e030051400b10401c50458000c0290001d02e01d15407000024040e5110a544000030701180000384410380e400c2c03148124803401500c4400c4401c85d0341250300546e2949513204c40c10541800c0900c1007510324094040d07001e0251618410414a0740054021003040719103505100c403411080c001030350058086c9146c900301c802d00441619079607400c4840c441d40184203014000600d0722000c1003c1d41030f12a0f156a241c43c0101483d0203039201d2098458101a201c030b4001101c0d10304c0c4461141c00c0300e2a04c0780da00e40400610340000012910b010b504402d00046040003800305030b40c0c0b560215000200040040c03615440054001c1c1c0ba07400d43d40001641140c1000200308540d54044000c005907502d10b5410038068864410f60012004d01d640f241d0b210381d10030496038860190310114550303280942c0c944103899512900c0440c0503600a070004a80d0a80c9070b003001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 527223273 1250 527222023 527222039
    0xb15030705031203240a14040b0f03072c04030206070f02030306030d030905010209030a062405063a0507300203070e0d0b010306200406080c0d0c09 65
    0x11400030041240101160450411040f1403480301410403030707003c80c4102500b1098149201a4104a00028000410556941101c083c602601d1071498462854840b640c1ea0b10326210700b901c46104805002408078038180520b100d10340c4110100100c0c41e00d40d084860040c0200c040c651403090f8070a9010b042c1074106407030301400560030f409400066400c00c0c4104001030b14001102030b8040c200346004204c802c0a410960b00900c1029480c80d0140209402013042c080141c104d03401507084400d00d03248108404280354910005030040300da0010040045881281e03143c0d010155118282508105411001a0100c6681c1103002e031002c0e10b544800400003000d030003c1c0f0080b28095429000090802c076030420340090f45031288800d20031640440421b007a10710a0703200c16442c4a010f04406e010000c90b05220315298000d00c41112a242090400700c5044480c0340703030080c6040400e6499003054201802035904410050904a42103818040030304030a000303025214181c0030b10348614403014188114 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 527224523 1250 527223273 527223283
    0xa051305103603050912060906100b0909010506090a1502010c02010606030605010e0d03030b060c0a060c030612060f02250b07020606060d0b03030403081c1503020d060c0201090b1503 80
    0x3164414004800c460710095041448030305000d80d261404540d5610aa030008800106c0c00c51170582c42e200d40e40400c02d0b00080001d105010f80c0e00300c2d80e5012520b1741d45200d030565128440700c0d40d40001084004008a05010001d400c1806005040c0c0c040e01c0d45070194000c2d09c2e1400409240140c2d111404042044c2d020301c122400740c941890180300f994140b0002a212021085c841d5014440f4068142d040c1071182d40a41c203020002801d2642d24040711030500d9880100800c10303203101e8a022082440c89000e8820001100c19482c11070b4003030700090b00c6000040082c401c203200b0040e02081901000800d02d000c00482e00f90f00280513142010900780070480002c024004030035503102d00f051081d6960b41340103460b43e05036115804103180c0180d1011900354015640000c1801c0c1002c921900000c017400d0780d0044003c1c010b90700704600170448200c03210b440c54502c0301a41041d50b90347c60740c2c04201c01c0c3c1c00040301180c0c0383c00013082c0711105580e12100c3e14011074820000c8922000303030094510741408 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 527225773 1250 527224523 527224571
    0xf030d1401030c0302010e010c2901090203090d0c0c0302030105130b0f06010e06220f170109020d03030c0314010b0319150e0711030304081e070b0a05130510 69
    0x1010125030760442d80c03240c240e03885900002e810700100b59200c0340c40380c2c0714410300c04440d54001c3d058116000078010390303900550346041d107800c0095840000304402c600351081d01c0c0300f548004001c0c102e62001c07000c10350b0326100e01c0d14290780c3c041404401001503142401800d01400d203c2e40d14a84242d8117003042a003071900a0480820048000c00b80005a03a01460101003800116200b60343c1d005a035101c002280140f200701510303012080c00000e010414000c9030000c0340c15030786440d0ba10008001d42d46003261520070b0025407140107402c01001280c4a58003110714104241000220511420f09015008909a0144500c074200000304003440c95980c85005600c00c51090501581b110307108001e81040550042100b401ca20000041c1e5652107008049510100d46059940e00d04160a04013107650040c0d01300e51510480450807651400346404a03080c07641c110400d04103d440d1001c000c00a09005445000301340038030302c60000031490078060101202801e200004154421103004094101800 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 527227023 1250 527225773 527225801
    0x1150312031a13180f0302010e24070e0909011a1005030c070201090509090105010501021509061501260906070c02061c020d02041509080f2d0f030d 65
    0x800700b0312148001c03051030640c0c181260598019040304258a000384030044c009030102d4400101074080c45070315907000c00320354041e600a11100742c6000095548004210350070026003950b1103007201003076920500940128140c540b015403c0303007983c0080d0380948290795048859664007200c1282c03c003424488044100c05950000340f143c024000034046002c018102d03642c40b0000501765085a2241410901424000b00101c0d00d41c10002034440c0280070074020140075100303001191040a80f008480c92207110484004c03c0c166031007040c00989200c2c461113050501c80d02c001201e44216840015191000600b40c5403503141c40d021a8048c0b41c01000740205091290782003004d40540c030b8460440e001c0b40f6280b160726100100345000d110091049107401d0809501c0410085a00010310f040a04400100c0c0e850b01c5116403181c4080e5216881c0b0826030b0f105a1102c1015607105401c070b04400c60b5001c3d070715a004124880f41c00c1480c00c007801c0341500409600001443c0350018410300c01d45804000304 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 527228273 1250 527227023 527227031
    0x1060306060e01031806021c0608011a0111010b0303030106020a030905040203060102120a090e18010e150105010c030203120f0906160e010305150d1514090a1e050115031203 76
    0x2a8000d802e00152107245810562141105205c01001151411501394007100c21955269003140001000c071400031aa4a0306044c1200000ca06605010715022200f041d0354003d6500c1c0c14a0064607640c40d21032a500103552201500c8000f5034061019600902254014042500c4c2c0f51030003c03c054020742069200d607105009101280e40e00203855003111000703618990303559170910000e0741c00031029845103504846100420141440f94180c1c04940d80c56440280101c3c01404101510750512011295000070701d0350040100358843c000010340d550080c0190303443d150000c05980b190300003c80c1c80c0845100c0310400e01442440801081d584a9006103070ba0080e010607980080040c401700c9a07146c10141c580340403856100304407502101e10000200802444035191510300ca0110204e04600781c154501f00c100300940c820200d4a6228403941e02c0502400c0d0704641c0c600d108544207024200894004000d5400090000d00c00ca481180c0424011803001d85546018055080180c0d9800101420 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 527229523 1250 527228273 527228279
    0x61e02031501170a090314070f02010908030717090a081c020c01180b030c0c0d020f06100506090d050307080c0a05191a07031b170609010b0d020703051201030302060f01060306 77
    0x1c3e60301481d00480d03501d1020520b100c2e281002c0f5a008010190b9000510340001e0807403c00600f004840e01c9240b003a00c48203c40d590715150b0648074010400003409442090805d500200420320092200000050050341c8180d00c801e50107140407140300a00c5038944c030001d00b110f82243c0412030080c4c1d400342460406220441d0307e84400e042c000d68443c05030016000b2010401d01c0351044140d0b1007440710384080b07031000c80030351200960700c88558034030346214003c14000c105034894140e1502c050b298003034100b9103800000401e214004803100d0081e02c5901042c44404c0001d0081002402513110b8000108014000c504240d410900d00c070b00c50300e008817040200c0c0c1700001d0b07001c2c2030300e06004070307000d1a007003140e9407103101b44c0141101298418540030303071840c000010343e0000c8132a45034036403054140480e9901c80301840f9580900703001d02407254000344003503d152801e1340c00801000e0302c40d00c2e0190078070403544281180e10000382c100300c0158100340108103211500c00105c0c0e0040c11039180620802d0310b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 527230773 1250 527229523 527229557
    0x60f170105060105071e0206030a020a090609050303040e060402040905040807061a0906010305070c0605161d061c02070c031a070806091611030d0e160819061e02031501 74
    0x10403105c0c020000301010070702080da0560044030b03044031500a00215a60f00d05524140000d40c00104860702081c0c60303110114007184a02c031990309903580a40114a402c1c1840000540ac0b00010100c039405a002c00c0b0109e0860450b02031640600d00c164840c6480304030a10b00300f41510030000c3c860000a004c0418072486648060300241c01c040203090000b120b41312913604590030b0004000c080d0205042c4014060b0104401c007580c034200303031a666004980d44070b1180400c1520b0082074800d0303004406201b0b140c19580000240d24041014000051400f1159034031701e10740704043d40c01600c0e40c4044644019111041d03d1240790b10000c0e0346440010340c90b00c0000a2a0020003038170703044001081401900545000754141000660240c08680c0c40300d840d0100c000160091810140307090060348842c0350407440c055a0310302034070b201c0d03405480107950b6000c41d4102801988800d890386600c0e00311680104080c05c46202910326000030240e603d15004101c03041009070003191f141000800c0300b00c0d1040c10 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 527232023 1250 527230773 527230777
    0x30d030b0d060b0d0204090c0504060608060918030c0d02030405100804120f02010e01060e1806010e1308090405090706030b030d020c0d050106150804051203060f22060f170105060105 80
    0x942c4082c000581580c10b8011820808039240001c0d0418074101244041c000b1040300c2c3c034211041182c080c841b503500d842040701c56240696005400404100125152000b00da80130a00320000000b124101046849081c0ca0b20350744460702070150300001424880e50030040c04407107040301141000c4159082035a1220f00e45120b40181408000c070f28040814094800c1d00209000354118000784581a00c5079000d442098043d00e401240c3d8400030a005480d45c8003003a00c1e4100c03591a00000c8455880080c00d0714001022401140c1080d42040f081d000c590b1a8407a2078081c3e465a001401c09a0801d00050100d07240e45130681c2c8607a01640e00710003030035800a0b0104108106443d000a00183c900e010340c0940426040210104a54489800b01c6544240110700c03403400383d0708880c18410015211101440243d410302e4029001c2d0300076041c80c2c1005c4010f0b03140c5200161007480f003608000701141c121619608400f0005101c65010080503209240e04c4d85040c811400070040d82c148500007a00318 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 527233273 1250 527232023 527232049
    0x23100203190509180609070c03020615010e09010b0a0908030f0702010c0c03020d081c0c081303021e0f011b0504170115091e0c0906120219030209030d030b 68
    0x103141e206a1200261240041e40c1c20144003400340303211031820946002c489401268018000c4052130005514503104104e161f82481c0c040e0050704c0b43da2a5050606042c410402c2d40b0360502291056429203501e03243c0b00300307008002c0001d0160b1a008a8800201505900d81c030013035142c0d00a211948580b0340c10001c8030003d42d82420701419200e0140740c544c05407140359201030344c8a900c40d00040203119001c40244010005030710f0b054140000d98040d1411101c01900301e20010300c0d8032001604200d10351303401e8440280a80103e6810b01804152207200043d420740e00d0360130b0b4220861071840d1a609000b0901380400d4280c11003140c03184a00000c109016600c00c0294500e0000d01c40c00c5403400a601c8000310700300701003104803031584a0105a000d0842d030081202018000c0c1300c0311a601140340f01d0080090000da0f0b54400182c86c00a00701d0314540072000c1400c003103600f008940d0320000c1e580a143d00014080e100541c803821907030101800c01c410803d29800313050420b01d141c0c040d030392114441604 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 527234523 1250 527233273 527233297
    0x506070c21030603080f040518010e0103080d091b1409160f09150c11030f1f02090409151103010806070c0f08070f02040506060a0c080a0e0303030123100203 69
    0x40c03050040d01c2240034050540c0090300314000001c1e40d9043c25004d40044c8142c400c20340c4c400e0801e1034004524525040240f091b0388501101800510005241000401d008500e103e4049207200d0642c40d081181300c0d101c1104194880c0c400020001c0390801050150030800446003000d691400030312483e502203024066404010a401c9100112406118880081c2485103480c10740c10741c0d0040040c010980b1030200740e4041d002e0902c201c1417890000703031848030491420060158005180b45851044020b18030f4550165000d00c40e0b848107895900c5094140340c000c030714082507403114100c003104544a00b60301f01d00c07500f01000140700207440081c2d52604100d080c50300300300c1e07000c040c01c1001c90220864070003464180006080c3d07050117995440c141c0c2490080f2010800ea8940d10204441d52182424580c0898200010030003c207100b42c01402ca164400e08001ca16504031400003820340d4000d8120300015090308a00341d602203a40d24504042d20802c2d55540c51780f84031010f02070b50300c0c0075001040381c1d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 527235773 1250 527234523 527234573
    0x40e150609070212040905102106050a0609020a0e0906010e01081807030b0a05090d0201020c120d140705071a0601091806051e010e030106060912140d05070506070c 72
    0x40d108102c40841d111a90780d4985d10703146c03140511400b40c141500d00342032855a0380408101611503a401d0040d40c0e01d188405a400384c1705540301405000000c04281c0341955401000030301c030115000800310f48003d03594041d0106105010840001d001525841c10040d4040d17942d23205036001620250000f02c0c15000402120f500350000b4604045074000410083c9c1070028008040d03050303045680100b01400c10b544440703540520072401c0340070350b0020116992103162062001c1250360002c028001c140030b408981c110348110f04021010083d20100005500016014140306000310320344025540000c1c008101d0600c1d20000b481c3c1d0820340103e034121085100707207504450844c4d00c068000c0c00d01400340c000020f20201c0c0090101c0602881a0101d0b100801e400c81d9480d0603c6040c1c00d450461b01d809101c241032401d694055050750740120348280381e42240d01529801004003101c14116542c5041d900d22140c504a801c000c00640b2180038044118007880c0020241c0d4408014800340c1c0702844 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 527237023 1250 527235773 527235781
    0x15020f061b09060d020c0d0f1e0207140f0d110111070302030c010503070e03010e0c03120429130e01140d05060402120c0d0c15020a050c091302060c060402040e150609 73
    0x1d0000d11542000c03aa2a2041e0b00030603402075000231038000340051740e031240a8081c4030542700085e8003c02c20000d00050308054000d0140042401400a4628018041e408445180004a00f28459041044c2c4100e01244c002c0a455a0701c0b04111100d4500b41c030203020709914503400700742e68880d100030031340c18480e000c000900200d101d191060441e240003002031084c144d1110805132151403071849076009014800d8403101c1001e030007040714104d8050340e030614411a61042d44600c0300006013040c10008004008454060710a45044409444020070002c05545041d4440c58800601c0c008580203648645030000401c10200d025540a038050740d50030000c090740d1341628140b00c1c06100007179101d03824031f41000034800d00000140a407006203400390251180307404280d9882184c0c546c002c100354440040c40c1006e09040c01c00e0f54000c00012001620700c0c440b580000d440340c00a180b401501e50149041100350300d07040c01009041451400034250760142210210103203007000340000d004040d080041 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 527238273 1250 527237023 527237047
    0x606070f05030a080a05070c0b0609040501090803091b01111f06090e031b0a051c030f020a030b01091418090a05010213030302060603060f01091515020f061b0906 71
    0x14000041d032140075250390703400c91000030348408410f83d9514034652500d00050190f07800703800f80d5011036800065158296942030100002c16a009200316001c0d52030740007070400070b0700020245005044001c00b510304071680301d1556801c030900d551280d040020605221074002404038210181108252240080d144d640401002070a40c0e03505c0740d850245824402c405144000c009040d08501e00c0e07081644003603102e4425a80c84600705c01c05441c81d003241c0c2488181040c8034440c041180b946007030201d110000e0780c90300350403a0410900c2001294490151400560b404881c01001d0180102040c12045000c4049065502240071070b481c039503400008100c01d80c000f00101f100b1158000b000350350301c020b800c001c01c012a4061008a0140c42204081403103481c0128109204644425180c100e41c0e280454580140407894110504101c00400200d005009222091182c1c8290f4000b00b21042501c00d0b11464644002c040c042c010074182410610541014119a801c0108440b113980f10b4542d1605 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 527239523 1250 527238273 527238293
    0x10e181e010f0f09050d2d09030b100e1b120406021c0603051b0d020a090606021002130302010e01120513030f052107090504110d1b08060607 62
    0x126611540d0040200d15203040540128801542d02c41d0144012002c286015003500e001d000b0050142d00688a4860094400d46e92520500320400144202c08428807040d05038281b61644100003401d0f80a040c070600461100e851340040622021a416500d843e4100503040e1016100ca00240202d446a0540320070707080544a03943c9030b0340d102540b54100b51500d140290301c820403001900b120248025074001042c800c1d003080320f4000c000340014a500302c12800050340341c2c2120035889440403199001513110074480e680904510400012240d080030070283c6071504400c0b44055140c01044030765034840b03041407488110f950a0800390281c031485001a5a10061010668520361911080142c0d02c80c0c0e289510030418002e8666209030300350a81c0c02c451620504d2405800619200941340882100d41d40d0725074088076034a00600e200b40c407400040c051384c14850407865005408107115400ca0640d00c0340150345125945c0c4034403101d050042c0034041c9580200410b00c22507000c034540e8203100f00c0460b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 527240773 1250 527239523 527239543
    0x3050c030417070f12030518120d031509060f0e040c0b030403031b05270301020c0a03020109060e06070914010c060f0c09051c0f08070b040c0305100203010e18 70
    0x1002256503071102e0412a580da11911aa034001c502d05040000c40078083c2411104d819003690f036081c40d203c45500c412040301d441c00007107500038143c8003591031009018400c42c40300403178a035030115840d0789000002060450a402400d05036140c400101701103141400000c0458428100b11201c40d5a6400d103000424030382ea02a6441c0c1d00b00000304420503505900000b01145c140f07070f0745062203641d00b0040750319009219122601c44a501c0404058a0b01e03000000c624640060001d85031030341d032440803404c00182507000c0300540e440d25554000c01c034440c060014500320190080c00145440400180004006e11403a842020800c1b48507070759920590f2402d8000d50007404c00d0000e1021885000020495882d80100260f0250301c042202e1602060000c41e01381e05100c144201c1c10b031915140c4000100c540122402e00c0100700c5078001540c40321045101d0703802181404da1705803035800e15505150005110040c8144104014001c0b00c1c501d0345c0d01c940080300c0d8603003102c42c94907141e002d51400300c94075 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 527242023 1250 527240773 527240789
    0x6040810050a020d0c02060912040b0301170a1220010e0a020603181203011d04150c020703150e06010b07020603130203031611010f1704020103200c010b040509030a02070303050c0304 80
    0x905c03400786142d000200d507801041c0c100125003101240f83c81a6600380241e00882d40450340c10001001040e1614103c080c900a00b4026681c02500969078038602c2550180001d0204031f0780206000780c0c07514040c2400340d02900780000c1c880c1d503c042d0065070f10b402d601c10009214a03004404204610a81580b1001905a2504842607515258003414240e0003d1081c10340c00d00c1c64680b1030021810b9400c010b80110351140000249652210000014000b0b1201d820114481c4180002c00700b0b000300c1110903109402c0800258000b41c04050500b4140140c00800440383d00304600c00050700d4a108813507002400305201004030443e88006070440c880c0b010011940003040003100140400d02c00d800010074401d8a4100350305459600607104240f8000c0c060000200502c0003801650207500700516041081e101c6030a024100c00ea081c00c19006640a0013182e07641d5030441100b800c2512601d07401c901080011801c103024030b800295525042e0000604000c001704000d55030600810550300508804 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 527243273 1250 527242023 527242031
    0x12080f040e01032d030206040b0a022b0b10050723010f0515010207030b0c1602120a06060611030a230c0c100824030a0f060b0a0506040810050a020d 65
    0xa0b08003c00c1c160360403081ca500745952100c0c5000c04c50140d0140b83d100c690705801401d1281d507682c48030f0728510802882400003036020000c044030007455005150403031210711003508402d2075401e0201d0440d00c188051901030a280d0546504054002d002d40341c00541c8a031440101b07200400420442620b14000c05d1704660030310780f40214000c07198010a11030030702202c40142403080c4800482e65404103100183c001c806d0300010501d0702810070003d140706070080100c00c80c2c0341c480c1d6002c1108001013441281858004981450800c10b80c0e01880e0020001c501d0040704c2c15025201a5860340300d0b000040c2c0910650b50048042d04461368408004a81c4006100703032101c40c1d9800305511110038441591041e9001c01c0c240a145d40101080c0e030051040110f0008028050320001c0c506200d44145198103102d1181d0641c00910a100c00d003c2c11480b0729000f04e0b4a031040c0342480700405140c0c018a100d04000d110a103c80c00c0001928620110600310100e01038640001440003807242644030081c80d810 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 527244523 1250 527243273 527243279
    0x1090f091407021c0c0c05030a050607080105010e1804020301090819090b030702032d030106090e13050d1d06031513021201120204020d060f09140112080f040e01 71
    0x1141c0d0003a1000d41880c01c0700d01c290b0355850b10403610390a00707890b1540c10440f101003040341e0703d100340208000c541c0700c1c034424103599442e02c00207460000165030881e201c0d0301000c20802560b0f40b02001c1c0c0c0c010102800d0500da450f00b01c400240701348464184000d0184080310000302556401d400010400703402c40040f0365500014030840c0c0060315030070803040101e85602c2d00011460b080404407413144203103078003039030500194030700c107500c65540e111030801942e881a5003050000d9222000718002d080513154403000520b480c1807d012160010951524038a0740080c1a021840210f0803020b107420074039004007440c040041c03440282042c00000780d00030501104020440030074480014080e2011201d004c494940500c19400344d1181c00b2400c80050080c0004020891602c5001e0804500c01003000d428000d12861181c111105c0b64030590543c1412001000318203914400c40041040502910042c1e41c188000303c0144001a10020070240700000c6c1000109490025107010f030111810858003541c0d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 527245773 1250 527244523 527244539
    0xf09050d0f0c0f020603100914070e03061e090f010908040603050121032006102c012d08030403031409130903051b030415030b090a0b01090f 62
    0x340103011400070550848806078010b01882c080e001090f4000381c0c5080854841c0d0902c191600003401e0150380d44091080452109041d024162820603a1141d4036560f00d094540100f24900510b54103000780c100c40c0600081e00784600e442c07244003007003180c00b400c1c0384c4880d10050b203841516002c000039540380c01c03454002c05c0040c0d0010411201140e40610103030345c940841c0b10b41201c0e40c03065000c3c42800c004101c4006405080c41b100d0180c0030b00c2c0014580c1c0e108514450512600300d03880314612011001c144000d406200c0041401d4441c040d500010700c041c5405d911075101c040c06490281e6486443c81100c0341104406450011050306204044607540e10505a49402601088020400c6000d01809485514082c2c070060040204100e420840401503030700100384281c01902003010801501c0149840c1b01d60700c0d030b103602c0d03400c00941d07840f49040392038400c0c3c1106040703d004241c10700041c00c1240d900e07040c0741900b2082d17103840001e602c2c121300d0060f1400b941580c055940181c01280000f0108 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 527247023 1250 527245773 527245783
    0x40311070f0e0604050112030e0a030c260c030d0e03070b22060f050426010513110301050106021c1e082e06030f060f030503090a080d0813060f0905 65
    0x10ba002940031940c0e844240400055940074014491040008500140880e00c2528640c50703409014100b440c280351a03444940300b00b91150464184038804030303903c281c0035480200000b40c0d0161103008c0d0024030001c0001903281e41c038042c4028200121800884810760b0140000700092000b5000c2954038407140720309074005610500c031074022003420344002441ca070044c3c0300600480705030f64500b40f600303042070603458507580342c2c0c04441500c07a410245440110800d200b218017410403050200500034151801020036030010303001d1070090b41003000401c802500065007021540d01151000c0c050051001c08490b11501c28141018074001140000c20141e00b00742100d014111055988a4180d11141102181c03140032200c01c814034003400c02040032038402e03400244a841d060101103002035a8600c60300c82041680c20540d030079080054299214500042146d006140300c0004e8600201241e2020f4070b14400100100d1513107041c0e5110008000b4183e01000f100001c040701040340802a0811950b00e03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 527248273 1250 527247023 527247029
    0x412030c14121e09030a0311070b040503100c180e06090a09050c10050906040b0306090603190f03052203020406080c1c050312070e090609011d040311070f 68
    0x8030000c0500c07036203600c0300420701e400d0340a81071190528119204104085040103840740960741d1609005021903035405100d50002c641c06952440c0ba510908507006007020038a0340075280d40d40042108125984003c5005040b0403040c000c005464003080c10159042c0300c00c1403100101214008000c12400d00358104ca90181006884580d62660f43c1d04108084861b0001c000e491036000300e450649901e030003070b40308030820b00300c0ca007c3c3d04101038640429026081508410340002000c410082c140c00c00c0001e25034040c0e0b08800501848a407d1805980111000d4003d490340070745589030011700d402507045a00380d0144030f203c01118404014482003950301c6d8082240314030700741100001c549000140d08061400024800030950f50303204c41c18a84064150802c0350b05020910501510044c40400c00b4405c0c0325944070b041e00c902400040040c0010020f05092042c01c1600040c400300a8682e1000310189007100403007a691030f581410380c5d8961100c88000340c4e503c1862030200307030380c03100e00200340803 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 527249523 1250 527248273 527248283
    0x170f0406021e0a0f020f0307060302030a110f0301090906110708030a240b071b0e0a0e01060e06010305060d020405090d1d01140d020d0501091a010f051b030412030c 72
    0x40110984018400d00c2030b15105029a0180302c202003c6420203002000041c40200365490040c0e00b20042410a916607000c807010a80c08010040b440b610341c0a21409030180d0241c032841d0100030307115407400d0f010602652100c55502d03020a010011650320900000030003504807034492031a4684032a40742c0c000c540c100d2038182800e00c01ca1001481c51505c84045550075110f18541d8204030f07072607182e40c00003881034400003502020507518824a00c3ea00340902030070a18a101450080c014506031080d0141400c0c10780c0c945070082140b600600f40403600071001f441d012810380c860200088140c201090040e41c410b2a00d018030044e0300f000200d80d03108028a840b1024110356451100700911225400580420380f0308050b0207081140d000101890503110400600b0589403044c20fa04480d0240c002d074610381c0d9219540142803881c3e0040c00071202e001d18294000d0514448000c14a01500142001d05100e042038400140410f200342c0380a090302840d441c1d4982140d04000f0100d440d814400c0c0c030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 527250773 1250 527249523 527249533
    0x4030b04022e031e020c0a030906050a02030f0a020a2114090a0306181a07200c060c010f02210717060f01090308272407170f040602 58
    0x3070044001407180180c80031081101041102c40303200342d0241203c1d000da40c2000d56118000c41900e030880c8040c0060540700001040c02d04498075011b824840540c000c1c074280720090010042c003550000c1114003450220600c16112000400140c1c03a2121208004240041e040080701c00e100020700748590407002581c0d600c055a540316552000d0340704103c0c3c265040300e10720b00c091000c11020342140c40750003e0b250812408050f00d0b00c600140091046031045418140c030309000e0469445040900c410010001001e440c51120608540e140c0150315554020180450502c103001000c0d441811444d4408006540d603140c80401c40205102c0e40904000c440c40c00004100c0151103040807004660640c00c03886501e488040c20014000da201d000c0700d04000b28180040002415480907140f029a884082c02c4011004540703102d00040341801c0c540180700c520384954012000ca13070707161424086d01200e165103606a0525000041c0d0b09a14443d42d0300001414032880c080081c0240101d1740703a0b500340c035 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 527252023 1250 527250773 527250799
    0x180e060109060806040b13051212060108090d08100f0602070305070b0408060c03060402070816020a05120a0204020c03190504030614070c140f010e0a051203100e070e0604030b0402 79
    0x104071003071406046030540c4154005000914011b0303025170454001c11240400000c20754070795280500e03c100c0400011800301f110250020701c42c01da070790480002d00b007926941c90320050305559540031120311020403501c18041b440c2002c0421220010b007208810201c0203070b031101c401a64401030b6202c200d40c18828040005442515141a54140e642d0f00c0e002e06070300e0b102c808910000d40c0001d0990f40d400307a801c0101ca0009402c51000b0100da6441241841c00c090f01d500400001603000d07481140541c50f5000503038640c02c2e0110b200d8200d1581203400507220440350410030300e1070141c0c00100001295041400000b03d400402901c2180d1007001d051040315600041c070301060000b03840000100340e14220817000550f0000e1031001404108044910304904420034034295591710f1b52119058204004450070f210b01804000443d4080c480910f14600704103100c0000c001c014403481c04c10440c0e07080410011403064489450aa00040003c0c0d01c40e81c0381e00b0400c400c1d10f02907804074803440d6200000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 527253273 1250 527252023 527252039
    0x110f0c1908030a0f0504080714011706030c060a0c0b0f06031c050d0902060909042001140a0302031f060807030c030506010e01030e03161101090506030907140604180e0601 75
    0x400180c440103030140d800e115040c102076419071303030000100051002c10b00003c180c030f400c2003043c0e40042410400790030300c24203588000740044810248080240d6412000c200040d2400031380b111f00200161011503581070036880446840400c410000c00a800300005d2203100803110004a000720000c034141e6560102ca59035915403c0134004211021500910003110079056591081c120385002400c50307441d01e0b0f0403000250644604070350481c3c0c1400e2071220001207450661001407007800071300b08560b02808144c0300d440306000d0700e002182055000800140000c0c41059650064460800569885a04c401000e0900311088507540006854800140c83d0300f03220b4014070b402503e040e12290118090f0354011001b40c00d83c2202c051041c80b042000c007003000d808090209960f40600c00a0751100c1500000400c440f00c641c0c0058422031040c8144501035a02181d140201c0b025488442e45044124002c00ca20307000303a07030080d50a00c1c03608021510040c52900040308495420701501c182daa00e5401c1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 527254523 1250 527253273 527253319
    0x504051914100903032607020a03020c040b090402123d050c030a050408040f230a0b030a0e0a061d0c030304120b18120a08011a030f0601110f0c 63
    0x1400b800074240841c100003007400b95850207410603254500c0d20f02140d001ea404044110141e074018010b90010840b18181035060000521218017100c092040080f1800041da1400e4050000b1b4802c042d01d80a56240c1c0c02c0c01c1012000040c0410031074542202d080008070748003010700d43e480c2d424501d541c1d061031000302d451058074895080e000d200c0342141c41d8451800010304c0700810031518a01c0c20080461201c0c0b80c00701c1000103100c01244940716a5584480c20829030301410000d004154101e814421400d041c2c05403988071550141c001503042443c407085243c4803980901402003468280441d03000190001030410345112807048540c5820440180b40e80ca1185100f102c48000340d2581d44030004800740b0059801c00c00541000401c441d0030713440d00c2d052180c48084a580c0890001d000c004168100c03c0b110b0040c19a00c9050140034610110500745120041030302034101c440d440011100d03801004070300310400340301c2c003190000302030048084d542d00c0803526020304c170300708641c10300000783c0800003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 527255773 1250 527254523 527254549
    0x6031104050a0308211305150105060702011805150408010e060412050a2a15110f0a0201091a01050310150915080607030c120b0a0b09010504051914 65
    0x4a11000f85151290003041d0030002682050349030800110004070798a6126a0080c0701900881d000070425103842c83c94a641e0800d103242d0301c102400108210303640c2105440c005602800e104c0280142e4a44018108615410141d88118410161000555a000904141c2d50303040020081c20031480f000c29a290000c0310020810b840c1c1c91820b0210300c7c401c001514240661742005800001c0003840d1402c1d00401c850221407030345c021210f24082c080d200055035040142d2240402640d000107440c0c00640c4107131000c49007081c0000681002d00707403007507000c0781c10250890841c0c0701c802613101507905102000e01c15a44a4801d018008204c42d00f41d20400943e00e0302d0b0441e0042e0fa0f4036003e28000079001c000c1010030302c200b81c024000741080c810300505109030340594001030313030f501c00280c058100000c40410342e116601d000f60780d0700b00707459003903000302034078600350000f5200d43d00303a801210702e1302c240e40000f90004200c064640d07202c0032000000044d00c0d414030f45100440c070001e09000180c82092 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 527257023 1250 527255773 527255779
    0x80105040c0b09040b0306040624030308010302010807200d020105090102090108010e0403020a0f06023a0f0b0301020d231b070609021e030d050a020c040f090203060903040603110405 80
    0x30800c02c040003450700103007540c0720302030000b042c41c0528100181c00c00b54120343c1654042e4951048001e80850540480705c2c0e040c000c062220307a5400e684004000c6201404000d040c445031001145c541030240e25458101e108400c0c1d0a102c075203503081219111038515402401640c2003c0120748003001c103009a5148201c1a0b458000b80c1e0329100c00c0c2c1c108400d0140058040d40154440f2001140340034a281401900485000d40d40d0400d400e45c080c401c800204044021810740e41c1c07100c03c09001142e40c0401d01d99140d40105120401000e220010010980301c9a859813000801c000d91581580080c0c070348450503d0300d00306034040406255a0100101c4d10102c011803000706800c89800300e007001d00074040c061000029942d10b15404140b0401100210154031462891600c60a280800c01c00428250914005040040038071700079548145c0c20301c0141c4125110118140d4071031280e8491411190000c0441e0030764100204005d07100d9202e4004d80b0002810040e5180c020220041110102c0e03c0c05 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 527258273 1250 527257023 527257043
    0xc15090c0d060b090c18240d0e030301080a051908070206070312021314010215011a19080609070201060b0a0e0f0405010620161511010c0305010f08010504 68
    0x1408000e48000c0ca00740441e1081c0d52100c0c07040113070300c0300e413402442104400120390340c0300f140c0d541c1040c1565512580302c0c41200c103009581c4510450401d011f00300341c0940303c0143c6506084c11038501620203003e2404040c031010000081028000981c56240350203541950300054241d068450035031042a00541020420040380c001401d00d04002d1584901910b000e0174040903c3c12076030144da02801c580e421104440c2018400342600300d21240b00c9510900041902003a0070b0810460b00e01c0c148212102d86a11a0341c2c040214a280201c0342c90b0b450302403e03100302000105000d0180700b420744a25000c0d0b10703040001040c10f4014032500055440c100401c2e42800c00741541125803001c1440400c1c5c00c1103120807080c1e01c0340c940d4042d0398081c0100d030700c400c05404c1143d20030803d200d503100c03080e908036032010f800740c4c140c049041c2044059542c0d0048035414010032201c1941c4040d600042000344c1d41c83d21030a800304690641c0414145c1d07030458001312403141d9074a68103080ea02c05581c080c1100640c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 527259523 1250 527258273 527258293
    0xe010905120a240203010914010503010b010804140c091317211005040e010e10090f060e010209090a0c1205090d111603030206040b0c0304031413030f03050c1509 71
    0x1c5000070f542d041400b00c44440140c48000300da4051303030400e0740000c5d40541c03500002074a807240c500f03a01d400b4060030380c000c101e4000e140d0002083c01102a0000d000c603481c1c46402e203803900040c000741034429000b0340760910b9070504007003640010b1500c0e4020b82e00500300d50182504020200304650280b25045500030b00300440c03082e641d900340030180040c400c2c508410380004864035a030045908074000c1c10000510b007440601c0041c04c0c2400c40c2c0d5100b241c6480c013401c1c140000d100c806400145031f0054000103a519142e20aa4020302c1903200996020302c0c803004021410711150840004401c046d900c5040020022800b83d0503100156440449034000007402d46907140f207150b4951030103483c1c2d0100c030307041540c002d10400302e0045a04240c0068002c84d0821040c8070000310fa1503003000100301003603c0c0d0319003902d0040c0f40c1500c07013040c08441c0b50006130b600949502100c14201a6130072504130507200d28035180c0940540e0004040c800540140c05407091008800c208441c410144080175062000b1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 527260773 1250 527259523 527259533
    0x8030901050d0f0618090302061b0f030901020933130909030e040606091e06050403020d0f0606090207030807020106270e0d090f08010204050609012d0e010905120a 72
    0x3d00b030000300d003a0756030343d0f0300041011580d4102d0703031108130f040400216a2000e090003410120010700b0901c22141c64583c2d0300040128004641c1c4411462801c607440781c96540c0a81d005e8030505001580c8030701c0f0038506042540855154051000098910080580416611000500600200c41c03903a20010030701f00310f01c00e072541007071034400c1c401d00c0d1000756031061710001000c854a42e00701c40001620660144600180360310101c01000003050703c08116403422500401d580b10701d0000900034903010b00020b0800143c2d0030200c0101d07601c04418003a1949402e020002908154016400101070070040b801c1a401840340744251820102d170f005024201e41d42e440081c0100600078070a03e41e40d04d6080702480f5040c841031450314141d42d180a0304525180c0455a8070500781c004504692040004100c140d46043c1126060030080c200344548204d200f54401e00e24401c006401042043d00c010014041c1c0d001c406005117020036282c656109072210180048182605c00c00d23036407640722882c1500418 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 527262023 1250 527260773 527260781
    0x1c0818030102071211010c0c15021b010c0e01030b0105120402040e0c040f0603020a0f060f14071208070305100e0c091207061101140601020d0c0827030708030901050d 73
    0x1a10140001d480d04001d55134400f40c911080e032450001420b0300c00c002c15210400e000f0500ca507a0b030791500090342900c50303c0d02e40040c2007031a60f80b00d8480d400518540c0b040004441c1003103518408000f00030b00c0304240e101428101001103641c3c0003e00e00000221198041e005455003c400440030500c0781c0d44a500380801400c2030f072001096072147d1301c2a515550340da40554100c11043c0e0310081509407462042c0940c40c852500138100e040c010300300070b020307a580c0011501040c544034a88202e07003644070f0010801c98030603000050000c011203c010968190400c800074065242d60380c04203e0741d0f450000e282c86072226401114001e0b196500803500f0443c447c0081c1500340002010500c0240940b03581a140ca12254402000302d600e910900c0020103007840b96401c1c108514850f400750340b0740030000075181da0312038080c0c00c2407043d29458803050140c0041640c08403898180c5803071400540070728098003503942076102c2d0304c0b03441b840001241404011060b10070007081a1074250418103500f6160001e0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 527263273 1250 527262023 527262067
    0x2070f06030509030a0f02121b0f190f0c090501081501080d0507080d0f0c08040b070906200106032f1203042120010f020601050109060309030e120106051c08 69
    0x10310500c120601d0034088c1c0d100401e2004502c1c01d0b041801d085691081d81400103101c070b9041076070000b130314280340030000b85001c08519078054a40003460642e85001c9440108603080481418603040c000309103184001520f5452807140b02e0091810782e6682c002d10350307845e016500940094001c3c03201400041011014003900c00a0442c086454409100d003c801caa0500707042000180c2c41c00144414413000032440c1e034100744079141102000d0300340717280504008200c0d50313905101a5000181120803a0039408030018680c040c4841c1c4c0138106000c034040b811400340b000510200c1d000d48400340c0c0c603e840d20504081c0ea847c00055401d00c0d01d0000c59046050400b06050110000084c10000050321003010b4101503181100e90058681c000380018040d5003034244980641d4001030050000d6070304980c080c000c0369007514001c5102d0325145001c4801d681030b800000d4111a268858842001e01034101d01c00f41d403c10b48030340e200511103030950014131221407005000b90700304114455036464014041014 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 527264523 1250 527263273 527263277
    0x203070605251a0a1407050f130305010509070509040c050f0d05030708040918022b0209040c0914070905100c0b0703050631020717040602070f06030509030a0f 70
    0x103480040400c1075414944540111a90181c9030003048040c1c01000c02103410a4100b002040380e140c0c03c0c0800c643c5c00f0b201601c0c8109000010400c60030700d101c00b408940740061882c50945c102c50752860031a0180000703440c0002507010b8018041468202400c03800c0c800e6800000b01c2d26401d00e44420700409820075a40690880d5814a0400214008000405d1103d12841c011640e8a07d05603035a4122921316524170003060240e071381c44000d6944c00b000446500e18006041014052030285160410b0406800a42210700c0c0330400c03050103030095410044803048401800b55003c01031030141c0b4a06d089400d40b003c00d1241a007032100341046441099519654240441c8241090704c03a200c520702d08441c000c1c000b1f5101c0e42048000c0c00e28132020390351050a03104d46140b001030b4402042c41000c2e800090411240c0c089000004d01c03d0103802d10202c030f101d0310007259880e503e400c4c009440f401d69020307a111520034642c0009000d4841e1241c00d22405420b00a1070800225243c00c8500301048150101 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 527265773 1250 527264523 527264557
    0x220b0411060a0806031905060a05180709060509090609070311130f20040501090909020f2106060d08030a0f060503070603090209010e04030c020922060507080907030203070605 77
    0x34890715210001c007203900240d224a52280791400c1090710301708802090803a11165064100c00058000810b990011541c001c00305455485090340304040d4018500e1a01c039101d584800500c140640c1e016005580c81a030700c110b420754507901034698640701543c0001e038a41c0030744010400318110078491420480001c150207805a00c1c1051041500c5006580c0d100311a43d03042e80302d141c82c084034070310104510058801403c01c0d280030000b81810700303144240d0040e00c0d00e80066000310766034410728103120680209400f1a20034210702d12128040c454010040b50300c20340c008901140380c881d10700204298000f240501e0359a445a1080241841000d08407101d611000c0c0443d07145c0d000c0c071030403010300460f0b071b00061190300500402403003940607400752000000d48020b0101080d0f0001804132903c0d0155040c40482d10740200c0d40c9403541c00c03514003150020450484078204281500728500070801990b402a8076216084025100c400c1444001e40c56030100e413080040c0c500680103455000e080310342e000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 527267023 1250 527265773 527265803
    0x3070515092116080c04050103081e07020301020703170a02180d030509090108030d060e010f09150305250e071706010e03031b010c110c0d0804090207050703020108220b04 75
    0x3440e141289103801091a50403c043c825950100a940001d4a003110309003d9545580c031225000c0c40741c1d200e00342c02c041f4641410642c1107860421510b01c1c590140085645600508000703100305541c2005003c08440000401c0c0241041d009440c021520390111184480c03603441080f8003200c24100460030f0040c14440064666034950755240203100c50b2016503a84d02421320000c0440382550045100c558600c07006008030701c1070001c10003d940b00448001004100c1020a02601483d54002040761081c2c0a4540d454180003d00522268003602c0f5602c4040c0c03505140d9403d20070440b62000040d0303060048080145240111681040040c14110b0058402c03101281c02c561000030080c2e0341c90000947c01020744024880d901c0d445046140100c1328510710305845071121900700f0654816000b40e031040301800303141400c46000746060842150f582d00300d80b0704180c44138024402030340400c0d4501c0c0000d0050706103280004401c107901e405084221210340e00c844a500024000b520b01d210600148 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 527268273 1250 527267023 527267089
    0x507120504030c021504030f080c0102040e10080d0e060913020d111207090803160318030f020a050a0b04180f0e030301080120180d0606060e0307051509 67
    0x441d000740d0082d078807030b203968680d401440040184684100e8428104010800c04034110788407100c0e00c5580010501d94801052001c0c501a000b2504070709607140c0030605201c0c0107042d0030700140c00c440541044d100480702c04081603590691601505800c43e1003000481042d10788840d440780b032014034202c014206400146041d0403100500d5003184400c40000d8012001d0070780c541502da11810ae4038006501d00d08000c040c9440f0301a03000500182a8021a483c0030103000c3c0e00107000c240c4a468488010b1990307811320302c0e21441aa0416030062000c5c842c00700f13050030000500404ea41000c14064606860085040f44842d42d28005a070295501c41d64130780c54644602905014003040740c01503460f5410181c0c41d42c21107400b0301241d440020b1107101e44040c24050002e94280c6002280700c40e001c0b81c0c0c40c502042c6401100b0034001c0005290040115080360400e50b1140d20901c1603003110300040d115424400305610700c01d01c06034509428018107805141c9014001c620100c084184070025001c4126 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 527269523 1250 527268273 527268281
    0x20d092d0905011503140705220519030b1e1821031b03061e0f030a03050423030a02100c0f080322020907030b01020a02150a030b010c1104050712 64
    0x1040ea906407000c0e0007041344583c180211804502c0080c43e910450824090151440c0f1a1201d0b40c60719282c56600070000d0a800780855008007000b402c0c2d020010060840b080081da400d000445800c0840d10200315a070b82d0000c3c0141c1c055030622060400c5481e04403c0c0c0569460002c1c03d01a14172488452100b5080110104400154424411912803c10380070107084146107558081403100c0034420071000340d0b1126003540f0381e0031205009543c1d08100343c01040c01c0100740b040040e094450108540b003016030040041003121002441181346044100c0060850705500d807646e60326030700144020006d490300020107042c107021414034210102e03071070756903e10b603090428080c3c891080c08420055080c1c200c441d1701a04150015043c1212607140e400a0b104d240e01521074010590b44100700300c0281d00030040c04080a030002c00041c904d40c0d4611121040d50f001289200010381000101c1c0a203500a12219210651288070340103041045400e00c8000c0100030700e80401c015a020140302c3c000d6507449 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 527270773 1250 527269523 527269529
    0x90d21021206030c0102150a0209060c011d1903390c0501030c1704060e0c03151e0601020304150201090c080f07061b0209090a05010219020d092d090501 67
    0xa0602042c5440e0042505041200f080d0300c1c1590410030040404a0300168540d07803000d4580e90042c1c40ea11880e010506c207015079407181308150b00e40f0850f03840b21400003034a039914221807800c980c0c10202072400300065081d00c1c407005020801003100038031803210300d03101000040b42c081009400d80b101c1c071003901c4410201102c151601e80c29074505005959250041010080050034060310364552100c0b1401c0e4180014000b030803c80c0e80b0403550403011000c1c4506d802c6503800504445c402204488506000310341544ca100b0700c0700003407920010000c030707104802e44190f905801440c00e0902d884140c0c045941001c10410844d5a41c644103c0050903a1021001520880c002003603103103148106075103030054a410140038485101080000b1122405001111b16070658880500d074990030f805034a40f1401d900010825400490500c1e001c1e0301140d0000c1c03003070040b9800c0701c1680070202c00958003184640100c1d004110548012064240d0f001c0c084244021882010b24490f076407203981604842003070b0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 527272023 1250 527270773 527270797
    0x20d02040603080a11060c04030f02030a0605100905060a0e0408030417040314010e0106141c06110918060d120c021003020301050a050406150806190801061706090d2102 74
    0xc42d44d0b400302c5500c038080300389181c0310340000d003010f041c400e10010407406644001046008454698011500c040c00309001070350340300e84280124100503080b24640415402643c002ca4034020020740c1d00d03e0718079420011641c2e0708080401ea51601d8860000755480248140c400a801d204a41105807010001304015400741035000007a0740ea0b0880d042c02d41c4c0c4410b140f0091681001c1092101c404c45001109a0000486180051884034041c60710301e80701250340941400e2508241121035040c000003840e14010442d02c00e81115000c1c0d00f120000ca0060300c107260046103104900c00083d20b0084041d80300401030500807402419a400607050114034503540c40040d0f00400104000c0c1407445406000d0403040390140545401c00d1625400700400d0b80c0c2d40000c001c18400480e40503201c0c14040049000c0c8170480d96041615010700502074000c0c0d100300800926149400e4561036400700c2c2d00360182ca400006410078000074441190300340c0400c04d04148142a10300074405c00c1d0b0141c40101381ca040c0300 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 527273273 1250 527272023 527272027
    0x909020d051515041406061309020c030702030d0206100e040c0b07050d021c02030f030703090c09050603121c051906030b180604121101020f03040b0f060411090d020d0204060308 78
    0x88000a041c010034414440d004d241020502c1c40200c450169071940080d05440d882c0c5c03250040700100c03641d048035034008200c0510002c0c040002d00710110003440c0440c0260f0485000d42c80c03c4e00203d0340d810003102e030740c0800c4440203024080500296211030300b05000c0c0d94900515078403881194000e86c8080011101948160210b82056805204c1e0095041c030448a00869400c003010207516445014a004040707100000003071200e901940c040440250001e401b030180c01c3e02c50b12428002d2409883c7c89102c3e00c2903403c00440100b01504488840c04504828003030113070000c441101502c00507100c1541454103441c3c01c01801e550b48130340ca0003540116104901400c0219046003154512203480036a80c0201d0308020100ea0301083d1907030b12191070310b4000129402032600ca802070040c2c0b800881c219000005000a010004038460300840000901146903203c81c0104000c550019402c0c4001c100180081d80c00c1346041c00400355803038000750000321488165400039044030a50380003154070900c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 527274523 1250 527273273 527273281
    0x1b030c090f0c0509030d05250305071505010f03060f0b1c0c0509100e04081e0a0206090d0e0609040b030109050d120603050a020d03030e01111806130909020d0515 71
    0x114082e03620485140d0600d82d16040e80c440100740c44104109558084c80000a502c1d800c140750409400c0741d01c0c4101544c00403025540c54010240c1c0e000c2c207829165120341110082c1d03541300903c500d034120740c03908030b01c14049407840e582e4501906003c05540c01541c0d55195000c3c0360b880300950303800703903106031080c14040402d2840c147c0300b100520382105002e400028104020b0b02401c0d030612046e510b0b058030450b00c90707986162a83c443c1c403c0f40b80c842d0030000e081c9142540404c106c4050602820942c0950b4115a110340c81d00e0340e1802038560440000d0601c036a401c005040c000300030a5001006007000c5011041c160109080d5600c4980c1124035500000b0343c140790315840090400b43c420081c10030322905240d6115030381d58000071080a407154034600500c0c41014001d0b170140340c504100100a001c0b05007901180840344e04019208070b00c620202005407a54a001c0d030450b0b042c4104400402d00640c200b810402c003c10100504a0300030001c9015040800c0d801c02022121150300d91080c00c6500d0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 527275773 1250 527274523 527274551
    0x2d02041e0f0c030e0a0b0604050405071701020304030806030f070e06030304031b0501020606010c08030c032e0303120207080415050f04080c2d0103150f0611011104121b030c09 77
    0x40304200312143c0740c200c0c00000c5d000403420861103400c514215008a1107444504000c0d08241450340500000846900d0100c031319141074025611490098442c290741e565500c0030f043c0c50f00c030a1002d844c89a08200c000307001414010141c507800017809400c51381842d40301c0d40c584100360308040702d03034807280e503645002c011a6034100804c13940010f0078a8540f80c1000180d5403400c0b2800045c040311600007002c00041c1800400c00d082115080f08003c02c4006c94620000d08030b00040240000d03400a004036007120480000e0713000300c0707940542c444401c515041c40c0100c4200406091081901045810000171903510a0740019001900b00d040c0904080d03000141045482c10000b001d030030f1803041d22a20340070465070385865945100400c3c00c0205603580544190019281c4503080070200c44411080412400c0c0d026100285035800003000b0070826000714040304180c01140f06402c080c0820481b04c2000510104008006080c07060040329200c2d1207907241c4030858102d800100b0070507680d00b10810302d24 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 527277023 1250 527275773 527275781
    0x150306031e030f0320030c0703030e0303090706110a210801081f0b040b0306090a172802070e01060509010f08091002070c0503030307020102072d02041e0f0c03 70
    0x41850740e40440381d0603840e0740280071810056684024107940c2c0e0400e07a10000e4980d01c0707407030807003052505a58070b1404d004140d5203600903540a42c00603240440300c00040c080041164022180302e0010000940750510840304414034008540d098041c20081c9000107050803015542c0091089160320400007800d00206030080592000b1a994005006042d03031000a0a83d140c020681450110b4010141c6006c540940b018002c42a0544910010004c080c00042140901d4034401e160341116070010f914030858a02440d0340c2010036401c88841d0011482440001c240b60120600569020076503540c900c1901c11802da000e0000301c5c9002501440542c1e204250f0300c605035050030281124100900480d0b9114054144414000e50002d8981c0601c40d150303030000000d050003800c07280d0764600031800038003075004418122102a52076180203c404102d40c42280240c000110f281500d0031180c0800c80074120004400401101800d0200340702202c900070314000120003000401d8030140000018100d07 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 527278273 1250 527277023 527277053
    0x1090b13051c050a080a1806020301090c03091a060d1e02010806090f012601020d020406090b12070f0314180d02010e030d020a18030f1506060f0c0c15030603 69
    0x1c90452503204003141e000010742e0190f45045ca485245030781e41404020050001590500c0000c040c02041010400c0c290000c40c140c524a0b0018041e68402105c00d8081e5500c1d0103005205088101d01c03120441c02d00d00c022a40200020001d00312240c0649031204040d04421900d80301464400e0f00b84195604405029085002680c42418528010f2011080000180140042c902c0f102d0352840051243c0080c01c2c61004140c0004c65540c0500e88000780290b1042c421140825090311000481c2c1e0311660030303030300c4d00800030800611943c1e07600c9003103030320003031840203401271650320821000f86072081901103200d413101c40300d0002003989200c1c0c01071400c07001094007811603050042c0c0c5000c40e440481030300d8011000010241c0c6078a5401002d54080d800c4148080ea88118401c000060165a2912480f907074011100514819400401c20060382e100b0300442021403260a42221820300c200054821140074684000c1181d03281c850441d6100318410650001031f8440f00140280120425040d5076 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 527279523 1250 527278273 527278303
    0x726070606061b02090a110c0106060203031f1211040219020a050f0d0903140319121406010504051e0604090e190b01051002190309030b0702160b0c01090b1305 70
    0x40300b200c684c000340210900811200483d52510501c5241c240000195810303c62841c000307001258032108029566001200c0048203088904e5960a1a81e001c0e4a04420380364010803c00800d400d079141d010202040030910358202d51f00704001705100080110742605081c0300c0d40582007410207400d20f24500640c9008810540c0c1140c124086410741003103902048076031082c007900040550117000c50035401040c0126560000921180c007155078410740f107079461240280c0130001e00d41c01d00b100c4840d42c41d08807246400309038100710038001340c0b401c200e40c85401010705410815088910010901a42096001000741500d13003640c0328000105004000c500000d00d10243d002e0301c01525444801041071044a0098080d00c1071107514510910074000c00c40c840c030080d4451040300e450001c042e500144020740e071141e080c4020519207403010441d00140741c070548000c4285420700f084101c01c1d50060340144699981d810b01c840002d000904050720411844881c40c00c0c4100d5400c10780d0030700103d501380804c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 527280773 1250 527279523 527279567
    0xb070905030607030b01021002030a0608160609050d050a060e0105060a1208070303051807120b070f090b09060c06010f0e180604200306042105040506072607060606 72
    0x10807034500181c03480c0d10803103e1074041425008200140d080048420881e50703d24000001c00c040c2c822141c01120403500184112811a400e05840e82c240343c00c1e6000e110005101804100440e01e0f00300c6004910303501a2041e01e042d04195950142142e11111108071207075101e408105580c9881c5418000810744150a2401c02919a50ba00706510a80400801f032580d500041981c88030103040700b08468040320b04070740300305880b4a9050913501803004222a012490b01c0090b200c03030307c104c400b00c1c5143c04a4403045511401c00304990441d40264112542140082c0500c213400e50f4100000381c02001c802b00b054400904004030004100002445050716041c107110300b5805403000034005a22940140800250054116600240012514117160b00d8800c100a03c014040d902101440303040f11424550107030140d0309002c0d80e20380030345d1242e51360110091242001080109540344c001540c040300c80811070101c54020034150f00a200180c2d9880c0e501c41c01070007000d8000c18154541c1c004038610038 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 527282023 1250 527280773 527280779
    0x2a0f080a090b0402090705040b04060203030910020a1e230405030106060c2003010b060d0209120c0d200d050a03090b040f091a04021908060f090c16050312040b0709 72
    0x603002c200090302c0240141c0502d4000f80005200c7c03403c3c0d4028210340c2410585e500d503503010003550303504181c1d8804100c1c00350341119045c83c0920f2084a0040d40191a1000d007141d01841c12094507034540b18400c1481003411801c404003070755440700c60694082503202e0340c0310380c1803009041c00c650554001d80d013805040c402c0c01c0c0200301501a0070807a1000e521f85098620800360100f8054003c0035602c3d60800804544c411108000781c02074403003440f040e14030038081010000f00642e141c2403500060f400141500e41c15000c1040c11504000c280c80c00d00c42c5501e00a14500400c5000015803c283c5694210545d40700c01c142e404000e050052002144182c00d140c02c040d400040c05a440c031402881580d90301d810b04403001111005244518000e20840d15954002c0d64440c08204d1004000c001038108400941c0e80d10b00724000c015061009480d8100d0781d91450403c000d00d0f8044a510200344010100030000520300b00000c2204c460811b60b030b0407041c2020f01d007c0390780c0b00b009080801442080d21080c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 527283273 1250 527282023 527282033
    0x913030e0907021e030f1c151a07020301091202030403020a09060605251520160609020a030f050a1e03021b18040506010f0b1206042a0f080a09 63
    0x146940043c5000004e0b40c42c0ca0f4907081c0f642c400c1c036404110001c000b0070001c40c03e9040c5400110302c03040c01e031018003142d018044180c180020901810301110501c805004500c11038002922003144098000a002c01d40c9441710710001003010107440060340005028070843c00c1051218009191058041c082c0c40d040940280c543d010300102c18140052216003000e4410050300300b04002d90700040e207201400d601d558042c0280c8003203910031030403c80d006042c9450a0700d00c13084900e10060340e0320b61091286a60740c0c6102800107103e040e6070200c52180040046140d405e0301e09501480f401c010600d510072032078001116610742c22030301c01044e900c2c808a40801d4000c24481c88402078001c8400c1c03c0d104540002e04000b02a90805c03079124503603400c2000b0804d002411506a070649807641c100d06030b45d101d00d20110b10551499681011079003002c01c149080035040751300c00c249041000040310562101a803188100c50b54807000180f4005510b4240300c0d040501160440010780741405000070688403 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 527284523 1250 527283273 527283283
    0x10603050f1e0c010513030b1f0f0e1503010603050f0a030e0d0b0703050903040810060509090102070206041203020a1e1209050a0b1605030c0604060f051b0d0b0913030e090702 77
    0xf6051000c0060b04600440c103000c030803c0610762250b0b41c00c545080c2030719100c90408049140f401101c9680b030010900c0c807042c421800494058400355856a500e2644500c0c4c8203488450042c6c0664131158040000b139018454400c5040c4540028032200b051810300a0100c0c524601c00d5002d1514540448003003070b00c0f02186a402030003400e02142d95110350241a24500c21a0b2000c2c4550003408000000b0700c4054001d1021240112410784464807048180c600300d00c90814001c2d80540100b0080040b101e110004112035030190050781c030240215215500511010030303c0c42d01e4040100001420000c0035805000011800d00c6c100b00b03210708200218805455a014100c410b20001c00c41c1e1186401d2104000d400c594041c0646e516140e802440380e89d24442580c1c1100d40508101c41e100c0003041c603108040c4140c8110101c1d01500c28512a8900340b45d00c1311070755071500c80c0c90b8070781807059840b04001c450040e10340500144100310345040003045032003044d12070341c807801c44801804081c50340024 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 527285773 1250 527284523 527284543
    0x81b070b04060213080708030a02070f06082403120d0f0e1b030a0f030503010f08010203060102030702010c060b120607090e2a04030f0b061c050709020a050408010603050f1e 76
    0x80c2c0143d64000ba4440407803007685580c04405144114540400c54180102c01b42c41c0f490780c2d42e022a040940c0310031403400d6040140c040c3d40b00180c1d586d40010306034807402d5145118041810180c600e04a0b191000c2030909040c0c8003015482c5100062000d103030a41449500424203000e5010003400c1c0d0740104081c1c4541703440207418080c01c0d004681207116941030008907412035125591000fa149035150181807600b0911541e219103048000c0020b1140d010b00845c0d1080360164091417800c1d40395801943c0d000304444042e034841c0d07036403031092000380c40300c1c550a04c034100c00100400c03062400307441c014140c17181500a100c41200703100c14040042003034500608500b00e03200300564204030f81482002580030b20f500291029403900d0907442409004e41c5500e01401c0c2c00d031307001480c51f041500c2c0d0070301e04005404014860b90107080104280705099002d000c1400084c03800d10b10706030741c0f42041400e50300d8507002560a82c104582c52415910b08004d50f1040016070400408a04001c000301d584546007c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 527287023 1250 527285773 527285783
    0x2f0f01020a0317060f1e0307060807020c040c030e030705010b03010c020a020a0504020f07080d0207060615050a0807051c0b030c0a0b07030507050c04091a0f0c1c020712081b070b04 79
    0x11000c14401da035422003030550b045c005021300c6250016035500786052582c1e001c0007402401804008a0018405e51a0500c01e0034190020034181c4440418800100800c20074075013055910146154100c0007170005042e0300307005100110b5030064200802d42101c5240c82040c06562000c2d2003000107803136101003101196012240141c503034450a400c443c0c18801c80380d0050920b080000e1a070a81e460030ba0250403d6402400e040181c00c0c0c5070041511003500442c40440440c0e03040c40f8200d036007403103962910b40c40b125503e8942d04041c4542c0740940c00c030a1401c1c84030140c542758000150310742000c11210181840c200d078445d01d0b030703441d01507c170ba01441181400790800c00700060403010301100b04108800f00303401510422135036089041440c1081c3e0503411220b04d29070740c18041001244640714540c01001e22110045c98145442d40c2c1303000020940d005000107a4080c8806c0c0c0204480c0c03124084070001039107030350000b0b2400c1040000c1d813400003040502504020b0141c0300c04a80782d49002540f0540c41 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 527288273 1250 527287023 527287067
    0x1c090909060b060403140f01020301050918010b060c1f0207020d020d080f04120b07020f2d030c03030615120c0a0302070c0906061d090c03042f0f01020a03 68
    0x341c01d022020700345094100742c000400090000401100004082042c0b500d141642c07208058503941500f40e00c020300c28280c9c0503071203502143c00b0451030340b20075202503068800000d8105400011840d1074020440b688000d402c0054903c0390400c0768000a508880807446c114902040350b400925020480c020182c0525941403101d410071542d0030451f114580280750030343d02d8075a1030200c4481c41b80401800c459007107041020980c40c500000f90302510740540d1020300303400c00091011484140a5454501003150703060030708010503009100a18601464402450b81d07858140c05000065240204180c1c10f00c108001c03424102404000c41604010b490410650b5260703600412070207406519070150007042022400590030ba80c591100040305e546840700c401040d007d2141000c3d0340038480300250015a504009000790801740000c541c068032510900c0d001c5107608611514141c4e0b11a12a1110b0420055100592401c0c80200c50301d12401d1005003490300039660020042e90315200b10012050301 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 527289523 1250 527288273 527288291
    0x20105040f03051e030a1b020115350102091c051f060518100504110d0b0d0b0403230304050309190b12190213121a0c09031c0909 57
    0x2000c00c0103a0f844c032100241c030707103038208800020014800c13104203e08901030000c0c400900d0707006010fa031002ca0f110641041c0407500d000f2a40001c41290300310318041603d2070b1200340c0421034500380c001070111a0400161039065050030700000f012208450340c40c0001c201030401c001900050350441d011040c83d520a00b8407071010340030000e080303180c00c150f900000c04211514011110104544101d2041076004000c6507140300303202c100c400c60704d04110704078070401001302e0b1802e154001c4148002e0240110b103070981c0c1ca460700c6503000c80035102100014810801c0305121021740da5000b10488441030954514140b039600d4580d07078410300e05a54000c40c2038081143ca00c0001502440081c0700c440314107503954644e1090501e14400c12500215900000208852001814801d8411001c000c250078030a513420100f03100761880c00820201e0f00303044111180c020150321703104002c2c01201c2080256481b0510341081504100888003030540c10500750000c43c003100e6004a5040403500d0302680001d007680 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 527290773 1250 527289523 527289547
    0xe031f06050907020a061b090504020702060f030c0a0e0f0a03022e0e01090807080706081b1204021c21050d02040806010302120102030106080a0525081501020105040f0305 75
    0x281640107541c091408010884201c0d0081004008207120700020408800906049030240b0074040401e000074411440902242c1402c0e130040200d0360000b40150f0504060903a00303400c66104844000c001d0801013464244145c03c4800b14807441001c845180700324070414082480c02140f807001a1040d0a01c41040c0b01100341da560950300d0445003c8614a1940708940c003420008810a005002800d103d00004442c080421078806540800c006090098600181210038082c0030b4003100e40c1e0803031160301015100d00342005101540c0240301d88002864140108020400035648501d0f0b090940002c07400025181d10340c1e0f018515030300d0213400c907854100108585078080c850001d241180b001401041e2140b0000d5407904aa00c00c9030503680034030a12500d24242d00081c865480070810100205443c2001a00b03e40da03c182000f2004d00880e003154040104c0152580140010a90141c144807204541070408001120280020f1003039091035a41c1c40e4403038101c40d00150030040d0119403501c41030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 527292023 1250 527290773 527290781
    0x801180b0c070b04030e030f060903030703052d01050f060306030d030513080c070509010512030d09020409151d1209040e03091012140906070e03210c010c0e031f 71
    0xf600801d02c00702524151030003400340100c02c00301ea4401c3c81a000038401c0d0060003d4900d11458801025500750385031904150040c01010f0100302401c94421580d41410800e4440e0b040c8031084c540c042c0c03005502d00404d000c586e10403d54074502400003002000581c0e00c00154200d520300c140d20300000d9a903070b013035801c551100c0b0044004080c02000260b50400722800142ca00c10341d43d003103c01a8059031f882c400c0204d600010b000e2241190001d00000700484815400b0f4110180050404901c4500541e16604407103090601c0c5191155500c00d05040303a081825a404000d031407400405091013070350b00c0020766008816a01d442140c03500c040000c140c4040c01507c400c0c02c0d02504024500c0307861030010b4940404640401ca010303185c000400c031301b40171440d1031601480100c405050180c0b601178084a00075122000150103205180e4440003140140030104000c0c404008001d440d100d04409150a6400c09641c80080005507030001071981d401094441034000b907203200075020301d150100017001e4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 527293273 1250 527292023 527292037
    0x4150e0a05040e0a0b33031c05120108120f1612021c0207030b061c0b0a020904150303080c03091606030203180105040305190216140a0801180b0c 64
    0x81c2c1040f0f6000b03880c520000341ca14881e841030410314125038a046d503c02c41d9240180d84244841c41654100c4a009010309641103001d070083d003900c01c40049645214031240c810101c580c00244001401070206985404442c003514200000c4c1842c000140c15441050154011002aa55001030302074500c0300b2a004c2c445040354001081940400074060194a415119004540c94a0b480e030b1911440b83c40032400364141c0354881842c0072103448020500841c003407007000d619440c800301e040d04804500d196407603903c00c0d01c2101d005680c0c0c041900134081942e5a601111001d210800b20500c002a0480840c540c02405410b249440356150442d96180030010300542c4803480c070f2213001085d61545a00254810744121108404401e000383c082c900301d0340c0480700540000c0003408511080440c114464404a400e48101c0d490801175a4030ba40c54603210f94403000495206009008a500707004001c140200320b008020032500e07202592040d010314660400a003110320400c001002c982c1042e0a070b50a03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 527294523 1250 527293273 527293279
    0x622180302031911060a0209060714010c0905120304060513030f0f0209010506032a0d110d06080628090501020a0e090919140a0f0b04061104150e0a05 66
    0x85410069182c0d40004200b00d0f101c0c11964201d10468024408603c09881c40801001070b40d0303403e1400e1000350424160203900071410007103030003c990003030340089417080348000000d00300b0640c80c0054401c20b1a60701c080d00441c41105070380011036011054808450281c00c145555080d6059003441a403210340000b803207288c1e4a030551051081c900780000041d031081e10460500d1340c0300c40420845020840c1c1c12140740e0f880044000912004001041100c039041c40e40d64101a5000c0402080d240a91482c4105840200c2c1400842400d4018000140b24000141045051240d2079001d1103460f509407600000e407110703002c61407e100341c2c0204800c513080b100840d01c031800c0b59002803000d018000e400340304050000c0410003800e00482c0051740e040740c1861820500855950b003802c550340101d03908003180038110f8001c4c080703002078006c0d29005118000c0803005180c945080400c555001c2d0000e1b29940c0280000d00c02c8078080d800b070a000c00c00307074140030385030511140010342118841e0b0400c0d90 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 527295773 1250 527294523 527294561
    0x101404060302090112021c0906020c030703031b08390301060c030e01081302040b130603080706050a0c0807120b1203040f08032b11070b0105030d080622 67
    0x3503040d0300d98003900031807900b42e90f9050880c050520381016030186a82c14003503860a0300c80a00001c80c945d10240d00c80344212030241c10304a40002e138030b085800090042d004251180d110540400b100d810b03032000a80346040403076182c140403034034070200d441c0071303009110451044ca00c031031440500c06481d007494000b1041d0141d6a6858000051254070182021000300301d82e407503c10b001358040ca55162098a951070100d00d0071380950200b1018011910001d80c0184414a9002c10304440380100e2010750301504903569100740520388039080b501c005003225811864008080700055000c3d000c90707040f00f110310b0100704c1820b140918000420b860303101e80d81d0040706491030f05035040022019104a4540500340c1120b0b42e521514991240304000c20000481d200140344580845400d46240262240359000618a443c40c42c0e800055440203c0c1524a500740b44010411440c00300900c0e0003049442c6002030705820942d0200702114450f10f54401c104402505101200701c07a540321200644250729251 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 527297023 1250 527295773 527295779
    0xc080d0603120e04090b06060723240402010207050f03102f0405090c160b040f0c08010b0f0418080409090b060604080c0d1509050706020105150906101404 68
    0x102080c1c10618440c00400c03d00d4100642520f090f21510829070340101284425035a024100661070703100390400c8a640b40c48428040d007030001101e01d6a09210385000a1545d80d5001e004500720100f41c440d0364032424101d00401c40142d07808620314086035020f441d0700030888110030001b030405482c1d01003000402e00e0900a00c03104040c006407290079400c030481049075039841c041d61042510450050a402421020200314080c22080091178a0782d224124200300aa003030b6581480190f06503403d8034440c405404007000d00ca405011b010050884400800c1010080400301e06040e14031840b00348100d6030b03000069070741e0782c09a04100c48542d208030625030f2151140c50b400c000b0a0214429a01c42c1109400240300d41008411201594883c81c01001c1400711401041040000500101c0d041c10590750304081241e0355008820b0014070038000781c0401402d0042c001d08650000304030142204e0000403a988a80350340d841c0c0c1c0e070409402c3d144141e815121101c203980c0307852500a50500395000203000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 527298273 1250 527297023 527297033
    0x90907020703030e010207080c21101a0405070c030e0a0b0a080a0e0c130203092b0305090712020603040203011814010b10140306031f1a09040803010302010c080d0603 73
    0x1d6030a0382d12a460f04101c803e03c030704c01260758a00e240100d2165601242a8031034500c0c00b20005041c0c0620034110312081400400390034241101d40c681341c0f1880380c403180c2114450013091305000c0511420707101007000e46006540284100c2150502800740a0080075005060301c0d50342e82c00000d842c2c81195555a10b40034880104491021111000030780d250401c00284c0c0200400d907005100002000001c5d1a81c1c00000d140003035202905d11800e600c82c214440e801038041c0070040c44a2010f90b890001d40602560015059500080c03002585800280c814804c00042c40f40804805405803149500e0b0343c0c1e01d2010900411120000010400d8561113039800c1103201d640c4010b5000380b840080c80740342030700828841c940f8890403044010440d184203010f0070101c00006550b000400070300f200c000c5034402404812140c1c689a21105c025150b031000c1c5140c0d48901c4500c40c2c0c54800381c421072181d18150311354245500040c040281040075401c030002c180440d00381038030310402d0524001c2065a80d80c2c82d06c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 527299523 1250 527298273 527298283
    0x10050d05250f09022b06080d0f080f010e0a150504020d0203010810060803030c0a03091b140d0809040c0c0606080a0b16090611030705160e0c0c0a0609020609090702 72
    0x140b800e00e40000b51000c0b807552414000c0d41d02d16041d1000722014030354046042c15440c010a001e0700318543c0c1d00c400c0045c00180410492194414a8460322942507480c3c3c8001c0c17085600a240d94a1a0711070b0004208003602001442c1e4808000d42001031400c001c141c84070515071643c4e025a6000b0f002040c0c8d41030408140c1c0c01941206c4c00c2c2c1c800c44a010842568980a5940364401c15400c1d400c00d100060001e849080113201e00003261400050251a9596050740758800c8000340e40f002240c3e603018003510206000b007842448041f503159140403426581c1011780c1c030810f03c0311400303291102034031201180140c14030200c40341e0207030040c0811610780c0c52240d65011219001e0707601d540181d003c10582c466142d030303070781075031081e0b0342c40281304c5081c540c0948501040380ea400e0301505c000c1201e00c0c0032840c203000341c0c204600c110713640a819a2030030250058158015215940400e02040000404d41d4002612000e40b98842030118213181c650000030300500485098036008400d08003001078803940429 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 527300773 1250 527299523 527299529
    0x501060806010819030c03050d060815091905060115090515120709140f150a03020309060c21091903020c01120e030406140702030304060206040c0e10050d0525 70
    0x82250f1480d400c040d0415954004c0301340c05001700c0c0083c140342002c03e100b08000c02507070070400320210307890756a8008c2c03d1926030700594800802c000340d810f1040e070400c140301004070144c0828500000c2281c0391110f07925506c06200f0781000c01208016070440b140920b5100000703000007405504900c03400e030803201c0c1c1a484504174083c28a6410300145030680076401d150300b43c480030240d4050301d0079070100b4403040700c80c03070100150321420164051a0100c1100700400e0420070720354001d0385908100401e5071500f42c010f000c46005076000e0080640d4114150b40341029440e24450140894642420b6582031010100c110100480e0070000038090580000f50510451420fa0303a0829545600c010720080350b543c2041c4800070b800400c000c2010f648251040034080805150640c070706025036002a03d10391282e404040940c0180c02080280a2030440020042c050307281041124039056095a030100c20b240a41880b88c2044114601406010000c4040b10340784440b498603c0340e2031031810f00c440f404d544 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 527302023 1250 527300773 527300789
    0xf092103050a060b0711012a020f03010203060d080307030b03030403061a0415120204020405180f070201091a2e05030705040b030c010f050c060c0a08070206280207050106080601 78
    0x180114590b144035216080407607800308941400d1907415610949a411242412410000c40c401030350799401042d6085d009071228180d46100107065807050220520350350388603a120364410f0040000c2ca0b01d40a0319018040c0d40040ca0960700c0da50302c8403c1e80104007601e100c03034061002143c04001c01c141603100001c0880880345501d0602e00340d00410055401884068140e419600c104000184c03400f4032680c00b4601c01000982400c1c3c441c80810742001c01d41c548444030301e02c000107111000517490350050f00a5204d100074040010aa1034a454001ca210600401d181d002070001c0c02c0c3d4245d00f8a4051105d6540412201002d8010a140b980311410301841e88203014520000510b0f2030140301d040000391014000d42026803802c4015582c60150203014810302c407042069000102c424071515110308400c0700095101c04614800a000603002000e401c103540c011028800c950b0369074000c0ca5210320211001000034186418000040d004840c40100745600f4040c001c50103110101d56503042c1c480c08 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 527303273 1250 527302023 527302031
    0xa090c031a0405060f151b03040f0f1a0307110a030806100e0d0b06011b0302011e02091807110d230a1403100e280507120f092103 57
    0x11408000840f0416200d0300d903c5042c3e00342003040c0303090082080b080b1214600c0303007034201000d942030080c5c48404d10b40005443d0304001014080c40004040545c0900121034043c2d2210341044000c441c8180b5028410a403046c2c0031002600c1580720f009888102e001c0c00c02036402940b554030780500041003e44401d403180c5210000f1048041c81582210f80c0d20000070b104a50201c0c031a02c4041540d40044d02140c104070f8a80d021207840c800071081c114126101c0e40c00055800c400d130941a013002d0380f080c400c149a5004200c150b410360b03641ca003800382c1984000711801950701c81582c00d850388108a81507114502604002d000030756006030300c80000b90002602e034001090300c408441a07900c1800c000b900420040344c607420342c0740329002c01386d94440000342e441d0304480d890300381b49005078400b11070500e01c40c00070908500300c514101c1d469440c040403031101071150b400c2c03401000e80941150f0511003025560b61001d0a030101154000c5441039402540d40080200c104100702110042140c91202090170 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 527304523 1250 527303273 527303321
    0x150b07020306090d020c0112090b04050f0709050402010e09153001020307020604030c0c0e100602160806014a090a03090b030c07151a1804030302090a090c03 69
    0x4040b03161300c00c000d40380d409055400602001540c0080304c04084480c0c060360307004c03800d0010f800a5a014011401080100580b03200c0c008030914010703c0760814201142000284401031360400c184000d40c800071180ca102540e08e001c41c07100941c00c05401c1541c000000b1000340020444140342594140000e01340f00844210405e0142c280d01c41998030200603844040006e0110b48035403564421640310b6042c01c4d02072079075018012604070301500c640b03041d00000385040120503010821105500103c5050291081c5001002610348405104903a0581e0400b1040f580003c280041c8002d400941500a600c07003140c880d844074844418031898604004481c0480c2108074000f429417441c980c50764a07440500d0401c0000203c9400140001d800c08200303205020000d003190030311400e020003d11000500861008003682c0c41c1e107813504043d018101d0312807202506010120129845a0141009644e4511200110351f900c0210340c4418003282c9420340c1c4159036517054100c0e0300280c10000c007000740032039 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 527305773 1250 527304523 527304541
    0x30105012409271d060a0f0f0906090c17030d020a0e100c0320032706030f010e010b030c1c15030f0b090727150b07020306 54
    0xe0003650050305414041546840054040c804403006a00c0c1440d81075694005903c01e09074003e40310b080c15440c180c0d10f1004030146103d420015401c104030318260000340b038015916990043c3c200881242c9131800385420500303940007030360307490007a20041082402074105000180480401181c258945100001751300880884030200d9510820245280c40d8441302420020b6121000d0703201401102c28940c0d1555071401c03039442101c1016281c0101d0140d4a181c018031040d114000a081a00003040300f800c603c00c00003d40b120000042441c4076000801013480d0508585c0d011050303848034000003000309200c04022503e040f6030740282e20051507602d404400580340011108213441800500c14491071441420120750100110000001c1c008500d0072586401c01d00b41d0010307211100001103082c00c03c01c00300d03581c81d03000c5115009840054100443c21702c038002c150348480e02c060441680c3c3c10b403903101544070711071a07811507500c031240c1903848041c0080740d0803880d0168404e02800c00050390040f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 527307023 1250 527305773 527305781
    0x1091101021204060c0314160b010506030907051c060219080709030305090f01030e0f0d1403042619210501061b1502120f0a06050d0f141204060e0301 66
    0x1d00c8021460400e13040c010101d5480b4000002602040f81c80340d1802c0200e0411402001d8480202c14a203014445074104040d80d05010390059008030820010405005808601401998022a001910700074182a42d500d00c0c1d090800240c0300c50f00c005019a6060441041415040c9903501c0310740641d910098140c44a505611020340818010003980d0001d2401c0402c28241e00d07814100043c00c048006402840d1000c43e4003a4545076006d4400c2458550f0041c0030900181c9003456914594609a81d0300f0312011054188100c2002c2a25982a07401c101c00c0165403d55841089050300141c0514005195036111007038100d220300c5611700050050024000e49040c1c1e403007920388102200360381c45e5982c000c5290240641e031101d800f03240d048a4007070a000400d55a00081000d0504d0308011107079011080010b081c0b0241545886420069522800d00b40200c083d00040a4481400e140c1440104803051252600d114012800541007030201070015100766840c666501115054680c10f0600b00c07 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 527308273 1250 527307023 527307043
    0x91c03080705130b0d1d0106140906030c040209060f0304060c3f020c010f060302040506030d120c09150c060e0c03060103060b0f0907050301090b0d0b06010e01090b0c0109110102 78
    0x40740c803140113001544112004240702c0400e8680060b402c1040410138600e88045400d904169454035410004500021503a00c03820000302d0701e1042c0350410200007a0f40d00282e04042f0701442d008903480101d90b403002e082e140042241134269a4a14140c50a10020b041d117004d014042603100107000b81e0742130388008008075460f205541e0007a10351000005400c4143c506100118240c0030419000315140c00c0c05138034066003240c0c5010a180c0d0852040206840c8001c00281c065030107600344110044d40182510f81d1105111000900c552030303500110385144454005c100505248040c0541b15030b803080702215414050300003000404440004282c86445502c0600d130705134403180c01400421840d43c0100c03501039005010001c11841400414443c2004466150128002000401c100081e038003803024030200482d41c4440b080b4a41e50b44003601c02028061504000c0312041c2d00b10140d0007103000c0c02c0a0042990322644410042040074007800050300107d800d00b600c500040c00d40e500008004041e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 527309523 1250 527308273 527308297
    0x423031c0807030b310b030a0305071101050d020c030a02100510031401020d050c04060f081003110406030501060b0702040f061214011118040507020a0b0109020f091c03080705 77
    0xc182c948030300407005401595940c0d68000c0b030030043c4410440301c4548901040e803000020300180846111901e003120900c00d6400d021390414600000081d40c0481240e9565900c10700102e20074110400489442c05080a480000e510001d51402c1503a0000060b05000c1d00301e60032200c102001c90114401d03540c05851139040140c42d075a084c030000f8025442c1d4000c0d0804400014106603074840c842c010303184180c401d110442c100080c01e201c6540d0009200f00c0b040f00c181800300403030804e525587c100f4000752001034140c44050951300215541c2c0d4001c180203580010003031000903265501a42c0580c0090340403032007140b800000c46001c03840f40c09000f046030146440e0404864440c0c40c6c2c03203120349e45d550096549550365010030340160b808102405500d120581d1346c601105110f010700c0102d61000d031005040d035024000c0c80300010888045075064a224413005a00c400c2e108149540600506419540c04000366600c4000240e5041e4140340c418040d035203100907034035821020385103481440111300d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 527310773 1250 527309523 527309537
    0x91603050c060a181d0702010501030305030f0405010212010f210503040b0c07033314011809020301020d09051e030f1e0304050d1206050307050409080423031c 70
    0x2100d460010040d0404800c41d003004c400c25110b120001020600c507421403a5421442c1042e419101da0407140c1d40c2c0c3c8141e081c0020007407541940c03800340071404000d0044c00390b805204001810031070290140c0d422035054000c1800c1c15619a244002004118041d14500307142c01d07502e901500d10450307941040c054004020714541800e112181d04680d114486070300e11031041c050000001401c0003040a1544000314140103002c1c0020640c110805006802481250400c0c039940380e600c0f984640c4a0444044400d6440c407801c00c0041f00e00a010011f2010754154408610640100c90f580c001c403401c244100700365901355000c451110354480c1c01d00300c0c0140076841400502e045e40c81c5000102120440b403614420a4038204054804c2a80103d500f00c416400c0006851103640c2c116131107030300f00580c1d584148045401c003008656166083e200c1ca512a07a1220b0030700050092101c12a8081c01c1d5008410602207504a00c080c9082e04518145000388124180e1485c002c000342048503074009150303035000d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 527312023 1250 527310773 527310793
    0x319030c170403050601090218040501051e210618031c020304050118233d0c18060906120c2703020102010b1008010314010b040c0809160305 62
    0x15280e044110303450000074004100210104004001c00d90081c00100740142c0d596241c0142603109604945040b030040b4101070040c0519903a10038910440032816469450305c8038440006815821800711045844403c4d455888151102041c190311880046070014605903150101070754900c241c000c1841152680000480a08e00c00c0c4c0046400038040c10001c120526200d450752070780300c00d081080b504810686400040302044503030980a465181d805000d62000c0c009a01c0d1003c1003140700301c03070400c114140c060040403c4042416840b00000f000f0048150182000341c10200d80c040c1c01e20051440a100140143c0b1549164003591031a56601d40300c1014100b00401411404582802f03110703800c4542e6245001034640c0c03201080d1070304901e070315071451030002a08545450851a014400d103506000c4680d401c101d08604407076200140031640420100414010481d0355216075015040605800105e680071300c50714000d40501090320050410b60810004015061000a01369002442c9007 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 527313273 1250 527312023 527312033
    0x70306140a030b010605071b060504060305091c0c0302031209070e180c010e010e03010c230c0604022103030a020304031101020c1203070221070606050105121f05090a0b0319030c 78
    0xf40c08018814548e0554041c08540034205079403490300600c0c00100e0220341081f1a41c0e15006464001d442180642000e91016a19426070000c04002005014048401104040c070070801c6910803068140c1c244414280b41c012b007629a0541d11070020b00d003c04034003141381a540344412803014146080109030400901c1c00540795104070070764030703418480b020910300d5058a081c001c800c00c1b0000e903910481c0c4401c51200da94a43d034040d030141e0000080a010118807002c1c009002c9400c540c044511085141801600d12240d4200e1003003590036000102c14040341c0e0710582c001c0c0d4021446516000b030440708500d000b508070700504440001e6580094048c00030f03101c0c03401c0259042102c40c0b050b612010310445000031944d50410f070b004420400020060309015452049102500f024a0114604460042c2c1c0700d00c0000054000310840c0001050106a0718038100c881c0014240904402c0682c82e004842c00000c081d42c0400d00e0282c028102100c01704201e60800600320b0f030b07140d1101c602008054481c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 527314523 1250 527313273 527313277
    0x20303150d15050f180c0102070b1b190201090e060108190e0307080d050708190b030a060c0806030105100807140d020a0315060623070f020603070306140a030b010605 73
    0x2070740c201ca1250001e5510b000d0a0145078420402029402d415042c40e4455900c82a0015000c081039001054000c0322030381e0100e031003c05c6501020040785c44a41000c0c80c0708441841c8164003500f4420b001e90f0940e4901d861000988240c001d0300c422402c03541d80c01440312214001c807000d60000e85108005a80000005007411412288180c001070b03020300f80c8842840d6600c9082d00380d4181c000810a1950100c45d405800d501c02118130701001541030940101c1055a2041c4010386c02540b1a0003240035a00e0800c407100382c098002d14244540070b22100040c0102da001c0e80c140d8003c2d424000020111203850040d80215400b41005203841468840402041e04140c00d415600010800d041d0015139105040f042c051400381e5074500c2c002503c11150700c1110450f0b80800c00b40b1080054528480032000d609100848a5101d0103030307554100c0c5044051081c907800c0081d40280e01000b032040b05640769028000b6a6280040c0050140c280f80070884440498803004081e1200e40005001d52845500 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 527315773 1250 527314523 527314549
    0xc1707240209061c1b02070f08210a0e09010906030b0f04050d0f022104060f08060312030901090b0406050618131202120a02150105040216060b0105090a030609060b0102030315 77
    0x81740030b030302c101c5a10300710300300c80c501da00603448450141301100505040070300509a0400400c08100440300e500606000d0200552092a006c103541c8611805404105108a401410340c4555a100c905210061249000a0f120000e07c01c5c001000060308841d0f4900484c2c01c980103041842c0c20b00f0003200c0301c103c010103090860103074618002c1540c0b00940008921910410741544031030615000400c2e43c0d0311513100c10100035103142030080c240c0380030950b08001303030389001801d41c0c1e0f0ba030b0848024094000244002c060300f00e044104420701c0303195441640560b20072910424065000c2001c41c02440301070720381c4443e0481c69580140021a600940d901d225900d0040c5c40901118018155050f08240891000b50b0062420001610b00c003802c0369000d01401c0750214200009400d00d105200d4440070011b00b55a61002c41002d0b5a0065081d02c40b0038070010303e811f00464903440e00d840541103141d41100d030141000d4101034558004400d0703922070301b980010341a46095000821010b503203a01 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 527317023 1250 527315773 527315827
    0x3030605100c02270c03040501200307050f0408160302040c0c0305030f060111030c01090605011203021b030c120a0c0506030402091b1c0905070504020408030a0c170724020906 77
    0x800c1c1c00d00c00b084e0040090b0b00c02c0c040d4080e80b607240d00c1c09040640c00c1d202c40c9490108800e00c2c4000040c00e0400f0314090702d4205240b490160345030f07141103907828014030441d041071120707205440400014520450714481a20b10a580621011a0031030003038800e078504100003004a5000d00005240075000e120b0903a200a051502c4a525005510210f045a00c24140381c4500e0751503803952018441c541c01041e00404c004888001c0043c0030391002504c03040e40c010f001484000380000e59420396001c018018803040300a1444008903803103071000d6a5110044c03c11204041042d000040d1480c1280036603114035000341c005c20050303070740d041940e04088002c10050b090500034806000d180d5805850640320a4454000080c0248070b41080d80c03901c1000c0c2d002c07912460042100703010401c00442940c403180c080b401c1c4003038607a589183ca0074625070440141918a03c0c00308000040c80300e210070f02c8840703960010300a0302d160b0640c1e0044040e449004045600041e0400450f80360b5030501d0b0b5004440d82c212 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 527318273 1250 527317023 527317069
    0x70c0f060f050c15010609034b080c0102121303050717071a040201020f1f2a0201021201060f08010b07020d02031002030105120312040b09120309010903030605100c02 73
    0x4100224402c0401c6c0c20a80004100c1c80d018010000055069120114540d5071400440d00071503a04a003800d81244103100e01040780c0c0203150300c0040c0c030386a600302a44200240d40b10342d00e101c200d50013500040408103194000c240030501a07500c4014920490750142d842d18a80121a1240b44982c805900d078443e4511041020744081285540100000c52115800d0303c0d250038a40002880c0000101509888d030b0040706c000d92072580b0403074000c600b44c0040a008030b03443c800c9280d41d91422001180c9101a01c06501d06049100d6040d4020000d0092070592442540d881700c004440200a4548010220b5900c20041c071000320a000a00b5000f80300400401583c2800d502283c207251119840045480d000f20040c0524600600c0e02001859004021030400240c2c0004080c4614040e00c054004010f68005c13400300002840b840c0c5005003541d1201d0303503900344a0001802001c4003501940024030703000020500780380c41350008000c0001903640c04044e050a40030817002c2222010312801c50101 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 527319523 1250 527318273 527318293
    0x20306040201271413051009051023091b0d0b040230130f080309010b030a050f060106091508090f07060818010501030305030103060f06030215070c0f060f050c 70
    0x5640c1c40320028050706400c0d042c21503165010b00c290f605e44d100e10942d5640c104420819a49090504007003200e42002000c1401d407650710035a080001c00d50401c14000c80e030600d4010184000003e4110b6540065400e1440d40e91041203203603000306080c0340011500d008220780081071035150006001914001c00051403d0003881d03008a41e81d00c01904460782c007516071411003020007449a0030741d002446034192000018103a5803121520441c06000780111008004903406800035840a091038030003030b080751a04666802c0056680e128249800524850300303001051446c41a070700541204d280422100d81041d9580c000c0c0c42081000381a100c252003082410011011b0400c481001004203480c0c8031490b042505018094461410f03152201d6810301004000080d44081120f0442e50840b03400150800c1c5000b1f15400341885602c00b0f03505c04c031940707201805140608001c100312031041e202d0450540e903402110041c241c603480340101080d801c3e0101034050f80114002c03e00944200142c5004040c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 527320773 1250 527319523 527319587
    0x308151309030206010f050604030818090f1006050702090610301b0e060a09120606060f03061512060801020a1e03050606070f05210306011803020306040201 69
    0x8000311190545a450390a008140341d0180002c2e809003a1003019005114103003400b2a10b03a10561000421801000504007160b4640301c40829900000030031080a034145105164a820403c0e50550700d0f00604010000360303580a1000c407030010782d02400e0800c8079910403040100603a06c2890350010b0101035075a1104d44c258a54018811800a19030b42c51200964a074000c121341824a2108d014602d008520503840d4010243c40300c00d45044a60982e02c01520400700c1c0c40728000c0d0b0202040060303a40e071440401199401c1481600c2040c0c0c0c50602c50203419000b24250340c03441c441d100403030314180c500505c0c0c0f42c0b00d020810020501c0d03c2001c150140d03190000c3e42241c1c442c00c0548000f40090b05029401d01d83d240c0443d091001605d014480ca060103c0050142e2203003070790040504842c51340c14001c014041c8090341c0d50b25840b160550081d1803030743c858016076008403030315400034051410505504503030003221400c3e00d801a0061600350b80700c1e8010360320381d8140c1e4915960811200d207000040d503 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 527322023 1250 527320773 527320789
    0x71b051c030c020d050412120c05010908071a042f0a080c09100e010e06040f0203130c0503070f030803090c220f0209100309020f030a0602030f010605090d030815 71
    0x10040c0d8002440c44985600242001d0303513040344500700002000200030170700310f00c203e0603030040d04000130a094002185081d01c08290083d001020780d400d000d15542440b546501800110307001b01c26040c00040f40c50000d91010321b04a034018104040c0c5060704002c3d140c3d1034112950f000444110801c69038101c0c0010b107003054981d001000036405400c00d040e01d428902066a0010401191065060f0410300e549030004014050042c900003200c1c0040d88179036442d0403c00000030440d008660b80e0404e20b018580104001c1c8007502c81c6000310070009418100040c00c401228050362b40282d80d14110323607a4903040d50000c0c102160307510035408a116280e032041009081058030401c19a0310092084460702030b9506902c1d0032501c90701c184035110040d10346140200c0014090700d400035181c0603620004180130012042a0741503c6400042c1c4d0411415500840c0540e43c45407404005a90300e500032036480c407800c00d205411031174408824000034000c2910340c0c4c20100c19044101d43c0801d14011034090 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 527323273 1250 527322023 527322073
    0x60d1a09100f0203060f0d0f0b0405030d020403050c090702030a090605031f0e01080c0405042d060203012904050a05060f0409180b07090608130809030a0602071406071b05 75
    0xe0f4008180580da01d8100c451100b040c50540c0c40e213103042d43e1929400742115100c5405020032480c0800101001028001c40c0c82c0c085840404646403603c0c0c0c180240e544054004681c0514410740c04602500c0c000002e440e0764441035904c082180303042401c100c80e150000b07011030703c83c002c01c8064140030075800182e034805400c1c14005200e841d0b250100c8a460000d507551494011481d007010300002c0b6268080030340c0c070000c03030300515140f0040400008a25009603403000c0c3c4040d1000c00041850f160414400170f44200b1002001ea00e00aa00c104010600ca541f01d100c0e03010307040318804c003d6803d15070040c100d00300d41004001d040c699a07499500c1615103060407100801990000102084118186190484080c1c038002c418036003481c0024005002c041c10440f1200040800c0c84104464042161410000036040d5040c102e10343c6041c6019400546086400703000b01010303040c4400303001442e24400c0c0242c0ea5496200c500042501034403601c031010135a6980100000b04420600a12042c400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 527324523 1250 527323273 527323301
    0xc010f060305031c02070b071b0b070216080303010b04090513080a090513022d040314030a090e09031c0b030a110406080706210603050f01090b060d1a0910 68
    0x2071340e840710403140c00307201c40e001081075840d105102d0803003c02e48600450382d00408900780800d12460fa00b481080c3e10000180040c502c24681080140003076010a5042202c06550a103d00b03140d11951129101e000902800c1150101884100b1040c0740b680c0200b60010000b42e004a484552511941003a82c480010300707003c503071441c05c204081e00304083c12549081a40c5011414480640c00e145100149542e508541c2c04416000d0802c4804100489000b95030080e4a042100d40d0301c62003545a4100d607a00c88040749585c00e000881e24044681144070324a00005103180403110450219500c10401c80b0b042c0385035942c54006841e4030f040219201c0700303000b03100940305400904108000d644440e00000103a80003c07004019094110070340c0c608526862200c0340d0401059103065000301415400a03055110b001301d0b2058200044d44091500d500440b035908442d5108400d01200c000501c0c5d006200100045182c00c601c46030300c0b01e0503007107110f80c0c003502d2120032880c00301c0d003d40f8100920176203 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 527325773 1250 527324523 527324527
    0x1209080f070b062d04050c0405032a04060f0e0705070b07080402040b010f1218020a0b03070801051f110f030f090307091802130204050d0c260607050c010f06030503 72
    0x621464500c84400404c0c82c440f0001c40e11481d4000d44d610200c820060090007180c036580410900c141060944015050180407610a19801c4000100002d0321400082c801034000f484003001d4241402070400341e0780303d4401d423981c442c9490043c1c03440140007440c032420040706108141c00101d1079400705d401a44143c1c0d03140c0060400340100000ca034940c1c0d5060b81409840c02292070441d40213000f90200c2040d100000035401004401d084101e00b5031034009510040c0c0d51400300c4c410a40303c014502520301959a8160f0740e88400074440244003040961116402024034005c00c503100390092503401c051403013903684007409421500d2543e00400034074110300d0004522050749083c108804001426600700070300610b40001e00f42d58507180400d4000e030180640c0d0200c20340d50425a0100d800404000d0007050b000800ba040001c2d0070001e901540c8920000300009851400c0c0c40c40030758001841d0f490142c801922145015200350f84450a40c03100755490b0000050a40b2040c800c1e03100440c040c402851b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 527327023 1250 527325773 527325781
    0xf020a12030e03070305190201020106050603101a0c0304051215041113050c0414060c0601030303050103060b010509031f06030f0b0106030e030a020a0204230a060320011209080f070b 80
    0x10704a2481e02c1d20440c0681d20009080010070300010300d056039503e6190310700c2c2a510303141c00102c0c0036220940000d0b4024030000180108038080c10440c1040350210794005101c01a10138062009204000c8094070b0317a8070034031041c03280303103812003440550a000f2011611043e42c00c101c468955401220103031800c450081c2140300790f04003c0004003583c01601c2d42003040c1d191081d0301005034015130064160200750402c812102e81c8034802111222141c41e4119502582d60f8a801400b5041c00d0100b00c45803820315034812020350250301925051040140a482008040028500c00500c4442100034a540320400000416000400d50349958020000c0840a40c1800006400d0300e891404000ea00c1d8000c010b074140103507010032091f500a03412500450360309044842041ca00c030000e1001d104900c2010103000da9112258000d10171030381f08044503c02030200c2e0030461800450800b00d140881c030b0002c074580140e80503030312521100e44118040b07400c01d965840c5589058008210071562011010180 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 527328273 1250 527327023 527327027
    0x110702040e0f12092206030803010b03100905010806240d03030b0a0503070b0d0f0b04020408100c0305070e09040c1d090c0303091518151206120309010c0f020a1203 72
    0x30b401e00080f1071100d140340031a04004104a04101c00b5541c2035822000d01349410135100b41c0149004580011505440c1e50b1100c1005017594015140c44c0701210105100081101a80c090301d81222804c1c405441d85a80300340c40710030000c08100e10a9841071010060588035511a0144031341a8040da60000c0c0d14034a000c180000c00b00e854001394440d52000108020400302d11003150300b41810b0003004030300c040c82600342c3d0b00030b080621244ca5000c0e0020a000c82c0d09400000c809214042040092040c81c1090000341c0840758259480ca00242c00410094110f00745441e00c0341c0c010740319205861303c0302c2c1d0710f100d28102c10250b580512010780002d014012180010450780056040480186141006400c00500f8071644007000c4101d00902003507400304414403482c242e1b11060b01030305130400040c02200892140d03001b11850605c102d9064042255400c0013040c04819010043c0114504003a190044d41c90b030422240860340c07c140031541c1c000503220191540010500250480e4100d6020311700 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 527329523 1250 527328273 527328283
    0xf010b04050c03100501050a1101060e1f050a120203030f040605070c090c0507062a0906021002071104091e05030909180c0f03150103120f02070303090504110702040e0f 74
    0x9410b05401d42030041c07016402256240c0b1046801c03d0a10b03950f10800300c0401d9502c10000c940114555107010b60000c0c48001098049214100840181100560710001d02441264601581ea080401c42c803041c001e020724040032003036003400142240d0a05401c036440c050b003544550452400110080760070001c1007403a072030301d202408480d00140103250110f14000c0c000d01500c0e6000e800c4030389541e2082d030b100d00e5021802e900d24420400001043c401d004029111116070321135100103100340150b003140c0351142c3c800c1c0d50980358050a00c8080c0e44000d4100001760201410549036452501c0c03940404a801c402c282c189544a503010716101d150301420408840c1c030081c10440f600f0342021140e01c00d04400f1905244900c0c3c2207075101240400700000c20f00d0005242540400c0240e1400080f0074454511030795035400c0360036621500307401e05110040b81c40345590310005000c9881c0f602e0502c80c62519410075818090611107003420024560002000e07540003c0b41d601850700038585651130218180a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 527330773 1250 527329523 527329531
    0x3070306020d022a030904180b070c050c10050313050319030c02010b0108010e130602090d06150501090e010308030603010b060711010206010e0903090105032d07090e0403050f03060102010e0f010b0405 88
    0xe181302240c405100402d451703110340601540325a54805881c0c005454007988d0180054202c0d808000c1841c003003c2c050301a446504040e94a803086080c81005498090403d020100c1c05659140c11915001c81d0007955809d804001c986601040c850080028592980e10300b041d11030b40c0d404034901d403240f1000390071105918691810400070b8401800003511009625410810f104c11880c007440c0581480002030041050b0a98050344681400e02800103680244c0240340c07809105017941642e039030042d2f5448a0311320800d108900c10600400215054502443d40100c000c0c00102d0000405000107031560301c01507044814204d12800c04807070f5681000070310b01501d08140103084606002c50595500e0240303560150401c03070008006146101800c6031300444d18010f0201d1500c00042c1c1c44801d0080302c0c211018000210b01c40800102503010b0f1080500854250315024030701001503019620591000307000034190764840c542916039035400c01071604200082c00001840c61b205a040000f503400241c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 527332023 1250 527330773 527330827
    0x62b0c0f0b03010308070606080706230403020108131a04030f0f02010504021c052103090d030b06091c0507140118140402070c0e07230c060403080603070306020d02 72
    0xd0410300200c61100101d905407500519899140c0070540f81c010003415a03a00280480e001e000c100281c2960400d2108915822084e11040e0f002411505010700f40528031000e80040e005401044e07086061500c000a00c90060080b0540034031001035420341080180c5085000403c512180d594940e800010403601d140c0c00d1000784090300380798002031401114a040f80d002e20402148203420840c04010080300400881ca48545203001465003196907001207400e081c0500440a451100c14484d108581d03000784010041400c1002003001e000603800610100180d4580806038031020500c10011100104203c00000122000c0d13140014440760007099001c404400004d07060205270140350012131410b809071801030322401c003414000c01244070f913400030401003000014803242d10750040085040700c01c10048450000c040c1c004011702485501c240c140c590300000c000c240020b108144141c3c00c100e00808581410307403240c49010803a840340c1c4176a0070706035000070941c1c1558550035035609124482 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 527333273 1250 527332023 527332049
    0x30f02100e030715020304080a1505060a030c0b071104090f0303060506091302090d0f0b010e0c0301080307020409080c010e0c030609070609060822060506040b1c0605062b0c 76
    0x101e000b0980e142c02d1402041e0a0b041e08100381c1803007070701c20025180106100c404540810b140d0f82003000412100e0070300140c3d02410b0400148550071301a480d0000c40303920001000c102450602c5000460708a020100d4200c0c4d08502110420303502c1e030080070351403030050700151a01c20103890040c0c02c0303451690040d40520760a00400c0001da60390748182c1840224004c015944c2c00c40c030f03030020f0900341828100404a981c84c0c2030744000d200340031150302d040e10340c001d80c031248039100c1c1300102e50503010074072a800b0784c0c2d0700410081d070041c06c00d904081c48a511500c2510f040013903500ba4282550b07254007010200743c3c403001d40c20f85646810420030350446400f01c060700c243e500b0020f00402011690084006000c8404080307160a141c2c1c18403190051540440d486404c081803804102811041d00e1a41c403a80c100300c901c40691070024003e8484201120040000490940d9008060f00000b04000d901c004400f02840b81100e2040700c10804d801c45d0402d00541105070701e081e046a142c50b800030942a801 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 527334523 1250 527333273 527333297
    0x9032606060f03040204090812100f05150a090302060c030d1b080402010c150c080a1a360103050a03020d0201050108070b091f0e01020d0201021207051e04030f0210 72
    0x1074000300c400c68603000702020f075203582e00c0c004100a80750400700102081000100305110341409810b0500410081d45c40d040c5065903001d00740080704c020f00409134810925003014044070700c48001489046403a0070140300c9143c2c0c940000d050b03504110341d6006150000901070b0b008641901ca8a010004000500030020b110301034000c15105000300028180480a1568803c2c003083d0303001c88000320102c4500b0720002c01100d0004100c58020380e0580150750600e2511841001c0e00b4880784085c0d1030140400c4610304208801c1105034000d481d012000d0559240c1c00c024034907058400d1400f1f140510014040d10701140343c001e1414000ca0005800c692501f0300501100741d0115100080750518030f85681c40320708103400180344500c4003c14001607000c1e240d00304411608000c0c00d41c00d00000b602540c6281208110030703420b0b4815118001c460304140e90001d200f460040000d800d60007041e200680c40d90018980d0300c1070542c0250415101003036541c50440c03c501c2d002c1700443c4480d0b114038140882050b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 527335773 1250 527334523 527334529
    0x106030b040605180f03040e060d0302100c030b0a080715080405030702090601140c160807061403090c0a0b340b0711010903050405040e01060f1a04030609032606 71
    0x50080c2009050320b440f0800700d440040080011080c4a0410040d00c14421401d14030503503d82c0103204080105100900041c01490118182071643c0e0b0150007810465096404080040c10070310701c041c0a255407070650039202d84400d8802000b1b40115001011018207080042d9035040c6000c600b40208044101000000b800110548070480e605941c0c0e425607032208001a28000b11070b4486448070400444e81c2e1103c050002030480c4900c480c0c0c01d0903640503807586411600d8000d44d0140f800451001064040b61144003801598060121801d4031880320340c000004160b60701035440101040740115400504107282900207100701060320101c500c03a4005412401050003510025091400f03c1002800043c056a0310f28984040b0a00812100c1c001e458003801c00c2e0494004c46003e2850811004d4007200140715940540340c90300d005040b40703480c1c0341380301c0a124001645480804020b0100000081050045650182c841d0700c440718040c4407640001c129400c1c02c42010350400d24a401d0082d991 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 527337023 1250 527335773 527335793
    0x18090b0d080f04050607060f05010503120403030e0a090501180c020a030813060b0a08030705010b06071a13230d0c0c050418020d11011710060c1506170708010603 71
    0x694048412916100da07a829803005020f1607116039005400069940c1c10032405902c40104003c03440420000f030390f01d54090668408003280e4001c0785480400080c40824050090b0006100f402003200b8861a2a03088a4003a10401e9004091112000f109504850711a0003410003164403840141240d00760f07502d00500c1580c028000303000407454101c1d40420700000b50490501c4100240c0140384d49660340307880d2690b99100350f41c1510907500c0c0c04006002c525145080341e54094210400500318190944180392000010b4500300f44520f100680c0000109600360800031100300241c02220b03080400c140900385404240080100300d6415003550000d24008c6021040e10780c01d4a000404140c034002810041881c82c0b8061340c05201c0f2170b11030703040049800c101440710302e00382c0e44d600200703140320422038807628140c03110b8410203044401440640d100b58500c10040380141040b92014113050306d800304603002900042d4200c1000510014885020804071006001450007000080d1840c2c5486040c0c0e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 527338129 1106 527337023 527337049
    0x705010e0a05210f1006150f021002091923090c12070c02040c021531030c0b01120b060405010501080f18030a18090b 52
    0x28103041c85100210340014140d01c061605040c4040300700310000140301a28840e11a01c140c070f540003000301e50f01c4200a0b5400082c0e0702d041111b0645100710700c0031200d0a0113011034001c000c00350300081c90086130007031800050b200c20f0304400048801c0d0071032020b00f0785a8150b040116524004180c1203c000c460380104031a0104241c0a005422030200c400000d0243d0070700c1000340400344040e4850b44881c4500d001c00d000110b0b980058100c070300e920326400059010080031920207220441041c2c00580c040c3c403c0034641018802750342014010745c2050410500b50031880c0400d4060250388030790580c0960700c1101503858982d0060401c2819806640c849001404950700c0e0034070b84602c0d4140c403010b9580c62055510307170490180490300946418803031005007805203490f41c41071016000340b410942d00c1a040204200c900304041380641c1200c0c414070310305800d83d103007980d640814842d4 = true := by decide +kernel

theorem cover : BRFrame.Cov 527158273 527338129 := by
  have h0 := BRFrame.cov_init 527158273
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527158273 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 527158273 ≤ n) (h2 : n < 527338129) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
