-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4239
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:58:37.671013+00:00
-- url     : https://prove2.me/submissions/6d69bc58-4210-4ee2-b429-3bc092851004

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 762230215 ≤ n < 762410071 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 762231465 1250 762230215 762230237
    0x51602040b030c040c0504082103060d0f120e03120a1728061419050409050c030f03090a060305010e06090721020a1b08030f090a080c010506040c0f 65
    0x844028690122207941c14416841c088003d580d490040500c090004d81e10340b92074519003c03501d803030b10b81520007400b60044680042583c1841c2c0e0b00590747e02c918110b600d1380f25004541071160640e0400c1c44050700e001c081680350302c9401e410030848010a142075085411000309182d4161450258403601d03c00507840c1207085000203640780351a500a41108091403a4001c000e101120344200d181201c840d00c2e1b2070701c500304400c0d105203d1440310718106440742107088440142d41c01d08a40c1c1c038011588102d81c1d5240c51340610500304002c0c0200c00c0c002d000ca6000201005165071b80e50800d0070901c0c810035440340d004c00d440c1d11030b0240740d0483c2c807460020400d039102c040400c41c10050052120040005008040c803a0704425040120f001510010042c0d0780d0340103c4004185d61401d6003402c02480d82e40e00b00c03200050880044a0f4868251407020010345c0340c5102041c2007582000c0d0183c042c140101e00500111410b41c007550207800226801c0144601b084030547e03400e40c40d030a011010038241107807 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 762232715 1250 762231465 762231469
    0x20d090f0902072f1809070b0a0e0a090b0405090d050334090e070e01050702040c0e09010e0108070f030b04030c02150c01050a0e0703240605040906020a0f051602 71
    0x10f003055520410301040381c008040203442108218000c048007140b104402c0820a0510207130604140000c445411300925184403411b0b5145224030410312515000205400510321810b03600912004c0100240881c0d99582d580001524031005402e104525000100b04804130003c2c42491802c265110079007950358982c03410f0a0320115585ca51503401008010a5140740550b9012178154000d844060125042100c1d10b404072000a0929040c000d81003180382c026078000d02543c800550458020850a05443d411a444d803200341d0103a03008000f8200220b2042d00654800b4166150081190201603403011541c401206501c0040d00e04031120002c500400d10078081800880d00180924209086507048960294025010b4a100ea55aa800d200c01803030300d80620034038404100000c101842c00c43d11018001c01e0384242098000081e25842826011b442e00131a0040000520400001d8602d0402c00065840102c000000603540f01207150898040e4099071740100a10402185103407095003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 762233965 1250 762232715 762232717
    0x607210507051f060b040e040b0924040c0305010c09061b03090b070c0302030336061b0f160e070c0b151f0c03020d051224040c0302030106020d090f0902 67
    0xa200d40c00f082e100d00d03000c900f400d400c0340100f00030040d0301c1018403d485c1c0f5040a21a10001030f00942c4590000b000004881e403900220f4040c0c216900080800ba446518051540c20001d42c8001d00c2c035400c018050070f06503040b28003142203c50940720701c269810305d84206c5151451154004000c80d4038000300344070084d00000900001407040031001d440035100c0d00003900c6c58011034000d01c1e800020481684118007001144145540009112011458250b0000350a8003401944003030800740490420b01891080094804400044040e500800034080c0c40c1c41c181d048c1800345096071841075010403d1107104420b01141c240e0400902d04035522080c1c0403400c0204c000b680d16500c66030045102400901c0307401c0201c25070f0007079144c1490501c06441c2c040d04115200f1240014440140310140200c071203503400540c040c601701c074000030710320344046201c6072140c40c884400c1d001440c000d000300721523800d5401541659104d408840c08500300081c00c070380c0c81039240a07405001e990703074170104005c0342160 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 762235215 1250 762233965 762234013
    0xa06090c082e0207020a080c0a080312161209050606150309100f0b1801080105010605070f020108131e0b0a0603050c0609041103040503030f01060302030411011d060721050705 77
    0x42c1d01610300741c0f440e000a61a102d0f2a00b041000d6000401c20315520702e009004d05008104040c0910308001c034003111044104c2000b8003401d542420000c845c01e059200b0b03e4500030700c03038010904020407a01420000e030350388001c0343c00c00d0250b07030740a41802012090906583c4521a504001c0a0551b038030540c201c003410340358140c12070007030700c1d0105850a50f40d0b1640d120742c81c1071100c04114041d85400031460a541c03060f8440010700408010680206851010040c1150f030213082460940e02d0700b0300c1c110420508140c0c0039100f0f076640060305e43d400750340c12521404a80140003040c80340d100c440d000c0d02218078511004240f6030042100d41c5130b03070030004040c0030025402480002c0d01034110a641103164001c0760304840a400020411181e0341070042e50b1400b51a00703190031420743c42d144e5506101d4109810903281400303010940500d0a03c0321407040c41e10204054007998803000d60b840c01c11000b5207030406104079850b0000706002c00501c41c105807802160000003c00c04103900c0c902d00c1c40c2d510548 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 762236465 1250 762235215 762235303
    0x50429070c05100c0e040f141b090409060b030706030c021f0617160e0609041112030f070314071208100f0b030402010201151401110309030a06090c08 66
    0x143c4280c1d04811862044050481180d1030340c6144120706000c0000300d401c810f5406440c01d28169074454903805070b00c400d6910415008a4458803078040b401940d450040351609076101381042c0340402000140e4010b001c00b8481030f800c0703c010b0754039442c040d4107035140515140b00590002c0301140c9824100b00c43d0010220840d00000781da42e880340c076145109003000700d1078403541e07021907514a0305a40c1020004000c152032055080c0500b480c078002520800094000f500105484a0910030340e81d540b00600c9080444004495039000c000c10940d10a0b0001401500414542000603925200b0081124242c560240c3c03650007800710356000340e4284402400e40c0c0e0092248070b1000c640c642c142032042c030150a0034069280c0b02d2500e84002400d603000081513038011201001c041040da80c6051403070715030280c01d0800c0344503900314042a03465400f84820341070703041c4503000701113060040a610482089029406a003111900c031540d040d0703101d031144096050219007001220310380c100f0321141d054640b80 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 762237715 1250 762236465 762236473
    0x904020909010f2d060509010210091506050301020306060706020a0903050f0714060703020c01081f0e1006260408090d05060105010e0f030a02060a1110050429070c05 73
    0xc18001c0d1003d800c02008003403100c0c2c041c4000c0a1076001d4210700c4c40c3c40700c480409021309010f1001008800e00c03a000a12a01140e03010140c0c0c020b001b128038120380211708104c2402c0a044c6008948041102d00800514150000c04c0c2410180222442440301904e010700d810030958901009520040f0944100000140c1c04000030b2018088250356008000c014007800d81001040c51030918480081845402d04100340c1d400250045000d41618009081202d02543d82505c00719808558032041846901000c9012a40c00035043d02180188019442208610380b00e1900340c801c80c21195103c000039016010010b4140c0e041c1c60200e50181c4201426030600c0d502c60041101c00488640807110340d04040c1c0140072030350744195041e503406001c403a009402d00b941130103c2d40b5007003081740280c0100000070f14440514001e06105030030881d51401c96005146d511050801040240e808a50892002070242d0b00850009044442c41d880f1140c1134406840d541c40c1510390955100342241c440c05 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 762238965 1250 762237715 762237727
    0x2150f090a020307060206060108060906100f021c0201090b0901020403081603020703061a0f091303110a0f14211207020f2a030106080705090a020d02030406091a061005090402 77
    0xf0180002d40041095800501441c14420000340083c80b0051440e40034103804001c001e404d544a04c030184241010303090a84900006000c100d041c03003800c0d12040940c80d0410401a40f0580c15405214482d000d1001d4594903201c1402c1c040c281d110381d200240c480e0505111b60400080c8400500b01c9080c480c3c01101d1040399207584007426107035201428050402d17500080c1c1c1c00d50030109007000107031600300c17603000051426460021100c54040e0018040009619001c2d0f40304c981000035042880d00032040c07440e032070614904924000c0301c0c40442010f07401444c8151802210405484080e51800304025003048000a5440b014410081c1140214491050200c1d1011014400e46800d110078124034940340100d8840d170500701d056042e0040c06a031601004200b000d10109085050321011268a07889440c0c0e0030b0440e0190103044501e003480c03807000042c03104110340760b4080c80901d803040200d00ca80c1e100c0300006002c007120031100d40342c020590b4629120140c2c4628014449000002d0005040c0302c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 762240215 1250 762238965 762238969
    0x180106090c0504170c0616020a051c1506051f0201090b0108070f24180e16031b140906160b010e060d03020d051e16020a0602150f090a02 60
    0x140c0289041d80105000060a00c115004016200440154400200809000c2d000850080d1040085103c0352140380c0541004540d40c11f41d020004200080520000540d4806020140380d40107030211100e012050082d80140100d0050b04100c80006008124442c0300080040c201ca00500304001195030b100780d48000034030343c6039007103001e400314170004d081e6103080c8003048a001c0100e812400310f81c0074900d01c1c0b01350541c0001c0403101000f071528010030034045510389042072955a40040070b0342c03000c607810007601507403494859000f04040e503001e000b42d03140e00f400c180348081000002000030380000e2400c0c0540030200001d004042d8094070b00d525103801d0245281c02da04204000311602490b580040149081302280705400c040100c0d0392800c40204c60f0b80c00b03951800c050b2800418014046400503400110010040d2114241d105155669401a81410800c0c0c446181288035410b02c140100303180c0d1001416200110103481e140c2c40302d4454071712141c5c07501001440c840f882e00c103940c9140c0044e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 762241465 1250 762240215 762240221
    0x3030b030d020109150b0f06071106030f0a051008061f0803040e04050c1828021914040f06030203041b030c180c0c0b3c0a1418010609 59
    0x880820b600006800005240034440c250340d034040e00d1421410209429010381d1050070058030400b085421680d10090352070600b4009840c004140c1d0702c40c0004c0100652003010340c1d101d6100d0910100204900d9640d24407240c0e03550340d680154003603a8803400014203104843d071101c1504812000c0407060701d07517680400d1841e60f40a50400c1c23485544000500c010400c0420031080c48960468010304c0c2c02c0060a0b601141280050030000c50307095180d0340382501c1c8c9050310341400d100190b0205565031000da0030200c0c18281c001e1441c00004146c0d44c5070907a19040ca5050340e00352100c54030013400d01c1e03181000c100c02940018105445400d139030066580a101014a40e200852090b110341b0042403511040246014481c08412074680c1000c000b442115444500c08401991159403481e090301d400d070340c404220001c903030b29202c03141c2d50f00c0718288110308070100f00c04a101d0f82c08145001e56558041c08081d9140341c1300711500c500000022500500b4010101c2c1c500075016000012800d5441d49a0025 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 762242715 1250 762241465 762241483
    0x10c050a110c0604090c020c060c0c01140d1a03100b09130c0f0e06010206100605092b030e12010216020f0303070c0623130612090c0806220305030402090403030b03 72
    0x40d1740b009006c0401d5014410b41510190844000c0e00b416407084901c1d464030b80400840b030400800300c0a2007940101c0c00c05a030045c80540d0410000c21402c582d41c0020312648285061107407061213a060b0040d02c0c90302440140c954041c0110105844038140710742803140c0c0c000c08440c1c840c100c0c040070981102e042c0c0000d006042c0446890a03a0a002001a0801c04c2c00f81c40083d0305215140d00340004e64008007141c02c1610151104805e4600e00130000d0005d50303c00c10501c1903210800e800c0814560b210040b110322410443d0f030b14440c0c4078094441c80c200c1c07148030103580c1c01c20341150f510070140c945601207030b00411002c3c0640340740c000e055035600c000c1c001075000900800c032102038481c0350700300380030140c034089000450103860321401c7d1000542072421131251a007001000c1e40b982d1842c11260b00501ca045502c40e19060f17030f4613200e408541e100d02c8100d03078015020300780001c00f5201080d0500b10005007501a00c0e03951450325250240401d0320320090055003859160016402540c030104603c1c41 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 762243965 1250 762242715 762242729
    0x1e03060518070809030408030307120605130e07090b090a050c1c05041e08091e0607030207140a12140a0f110102060109020c031c1808040e0603010c050a110c0604 71
    0x601d085080541200f03400703404007450f035000b40000e01004070000200d03a003080d0a4101083d0040100000c10701401540d0485034000b28003410701d4140303080701e402ca01d00300041402950b200c03d4407a02c203101100c00480340e1a03844540c82000caa05143d25611180e0410b850340c044030302e00803070b20604240c1d400c0010407512410382d841c02040240f007418824600090460361b1500d13601074450319840320034000c100010344140d4910803010f00e4800c0080c094034015101410300740e102e0241b42400307515007400380303e003003400040a03051190926098945005581251001c1d010854403502c4060820002c001d940da607038407880c44480080790484000808c030134883ca030340e400c481c2030942c0020b0405130180d021030007150042c4a0f40d04001d60210550f840c0030b20142c1c2b0745204040300340c0003a0140030070048440340c101d000380d1030b00103010448001300305403280004001081e49070fa100b45170032141000302c0000010024400481842d00c2443c1042d01e42107200d00f210055008400003130459403103907101403 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 762245215 1250 762243965 762244009
    0x30703030e01110c0d1209020d030e0a08060727030503030c0a110a0b090f0d0f0c03020a060c0309020a0b0408030708160c3002100f0909050c070201110307031e030605 73
    0x964555802a80c12080d034031b02032414845c50059034040799a08510b040c1c000d040c4a180402070710381da12002030342401040690304035400707403c00d0f0310701420950401c0c4c5050041d011298000c14085040701c03100b000c0b01c0d80403004602c2d590380d803c00b072100d68005007506010042f02c0c8158080f0340b0010460300d00380718000c0d050b041081c03d16901d4145003260044048246402074407541200b03641110401080d460903040c040c000000313501e02281094040d540081000f0701d03081c0850f501b5641940010701080c8207031005d4442ea0346500c0004900d0146219502d50f0740e20800c00800040c0902000e00441c003115004103481d141c15075564024003200e6002107a46420000342c0384005a41d8040614046101520303a040035426900451030746c032419401507003440000c01d001e04107588110b011500800c1e40714010001ea0410581e1800907501c030007012380c0041c5082e02840c0300440007208031000319a16403109a420300f03010703c208580c203a2580404040c1590380800151a440ea0380b81d0000c080340c007406d82 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 762246465 1250 762245215 762245233
    0x50c0a05150f06120c01050904151d060102071401051602030129150405040e07080f071e0b09010c030908100e0d020706050307050705070b04090203160e03030703030e01110c 76
    0x102002d207004120910848003818282500f00300818050314104c2c00b0310b800c2c1e50b00c10154010a0150a40d50400f054003022180000341074118403900307030201c4505481081030364503a0341c0126a01c9042c1d008100d000020b20480303c10a40c01a001080d80326904410741031106c4140d0006421102c8924000c0c29100010000321020a5042c04088480c1800c840b00d0301400032450b407030351207030180d4024140542d980c0c190090f0181c1c004c0084030014204002101c00000f010076855032204450f124101395030941445c154142e82e03204e07081c401987c0c004a02e15040c80400001161039030718401c0145e05000c079018000c20031120900900380d10810724030011072111220a50036240001181311a021904250002d00032241c4c001c044a4003c1701c0c0f0716082d6120340881c2482d6060010a80c840c682d40c0c080001e002030145101c0c1c0103944181d1001500c101c12004840c0180c1c0c6000a10150030343c075400411411300080d0003503012944034110072000040c008882007600c00305501084450890358000030310 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 762247715 1250 762246465 762246481
    0x5090c09070908031e04030222050c07350c0313080d0503070818100c0f080f06040e031207051201140112110c06040b070e01110706050c0a0515 63
    0x20301030300105a841c12090140c60080556224000c00c01010015040c82c2c0191148208100a0f6009190010054501508aa40c519250340000e08400302d0003030a00001602844101080d86e10341c1d60402042442150200d00d040d180c414038240202d030b044d07004024442c100710050041c01240c1c5078800196640d0850b401a40c10700c000c0f40d0b0001415921840c401e64420384d00c0310542c0d0b00840340342031050081e261507074558500081210640c0c00b41c45101c2e40c40d0b0021a1a402520000702a81c4507001800c0705c2010403116100101e90303425801810402187c0a8100369000e6040f01a01d038040c3c0341884800c04024007012020380c1c0a00002d440810b0a12a40d03a203880d01e00d0040c5060082030b44402c03000d00010740300d280384800c9001c1c0c0e81c2d5158070840325030b0810012075840401402c00d8500c1c0789030620f8041c04404c8203441060014804d4001620654000c4e0b01c2940103040c03060051441600c1c2020440d155403003090542118080c00c0000400144200b050f010410440d0030803c50a14040386 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 762248965 1250 762247715 762247729
    0x21002091c0807060608250305120906040b070305030f1e04021017100e1008070306020a0c05011e1a010e0f03070f12170a1d19030b04060c08040804150e0405090c 71
    0x22001f01901b0440320100001080007802048032210380c0120381d1220b09100010301980207551013808040e10000742c242c01c0541c0840254403da18078800d41c41281c6031f00380c0d44400b0f9108143c40119036011400810094a801840703800d045040d460b100640300c850340c0c138450b141d0009403052024001180010b000c8110b26282c0c582c1c0c40000c400658550900c3c0c21009590743d41c0a01c00a0b100e642d00140d0060307014801c400480300c06800c40700a000c01105080d1004200078603500703562800e890a2084540807a4204641011210580d1041c10582ca40c0003008000c02403010525414455828009145105060b005006092802c102e200000f21811b00040c4106000442070700104104500c404c8203400101c400703d644d007040f00030401d11000001064806400da043d542c022040d2180010800c590310301d100d84a203101c2d4001380150852000151800802654000c1440d20705004c00d00802042c1c40c9491020401e80c40c02e407444045443c0800d0454800b070328500c00030780098140c21240d0030000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 762250215 1250 762248965 762249013
    0x603050105070c0f0b0403120c0503040507090507020a0b0a061517070804020d240e100b060708030402060715092306090601271103040201021002091c0807060608 71
    0xc100090003600581d21407070100d13000c034001840c000c01a03001c20203040c482c0c2c00307014000c0000803080040c0440c03c0e0019101d47c00440c0d0442d054800c60101080c15069401043e01800550700100070764419035903084800e1030010000181c0c907540e0140043e148451090307141d410406900c0c0d00840442602e004c01c0d1048005100300280705480c1e081c0030041c0c984001841c17403140c1000b0202c002c3c1c0485154030b0210300f4080e519202d80c0d803e0403080300d03891b00c7c00300318200070203600c1c0800c0003600c84103418040e40307004041010304007146c188005405414210010303c0c0c4184198117510744c4070f500c0b1a040d81214440c1c9004d0707422914151541441040303404000100200c144c0083c0032a14041202c25500c401c1401000f66103132503400400701181d401d030720200e40c0e4041d040c0d0601c0050184803d690554000721800c2e801803040c1804040c00d84003074804c071604c0305005440c0c00b0304a0481ca0054501031240201155400410803140c2e010611174481c0801400151000d00311560030083d104107205000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 762251465 1250 762250215 762250217
    0x90f04050708240916021006140111011109010c02030708030d060f0e0f27120706060f0b04050118031505040302060c09030601030f030c02030601080304050307090606120b041e060305010507 83
    0x403d80c1032501d641d44200c41741e1113811102c94080c401c2580760224200420990780800c290300300500800e0200c0f000c801e0300e05484c001c0c0d03504040004003014460981d0f0b0805582103105900704880002035102e010466450380c0060200c606c5a40d4816049146038011641c51301c82c10303a0780d0010302241550f503890f1401451f0041c0361015038180701041d40c03002000507064401810a07150310f0f02020f030307000400513031070b00d8503900365003a4050742d6103441201d030711a41080701c944e0302c0c0010102d8180c0320343e241101603440140c40c0c20306207814000103644000383c4096a079600e0f07100e4803000000030784100001c0071900446202261a0806280113490100301074154000c55006109803840da4800254443c11241c00c00c1400845240310f00301079400361030a040203501402035500118045100000910885100b81c04035210b050792407118104840c0240150000200080451540a21240c01c541c00042000b00002808480d10400201c201e07000454003529507265101001444828840e0710780c000c841d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 762252715 1250 762251465 762251521
    0x8130e09121c0b190909050d110d050a090e0103051b03061506130905072303040b0406050604290a0902040e010b1c0515120a0b010b090f04050708 64
    0xe5100301071101c0400000002080743d882043c1c00499850111030650207000320410483c035521010601c02806c0403141c26200d61094400d0101281d210b4800090400c0e005400344c6500e1a00075000c40741e550010720072400300544900045248003408048a00941c1300318000c12505280310008921840d0401c11a8825000101003000d00c421001d000f00d4400c100f255082c1d982e100348101480505031a070400c074007461805040140e4a40c100c00a0345030310b030400c00e41d080c480c5940b4020481d0391000f1200209031404240c08100050b900d50410350300100028008150348a40800d894198003442c1c075407a40b160300115040764039061450f40c3c040503046801040d0f280504040720720050820610a4505440002a0110708078403807208002402032010024046410046219025103021072412841081500f00000751608001a0035554990010b11301100340e00c1d10381610000d070440c1c01029082411403603004116540d503c5454480d041c0b40d00d07000c0107410074010800501000700f40e010000c0714 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 762253965 1250 762252715 762252727
    0x10c0822051f050f0a0201091a0f090109030e04020d2d0614060412020a170303061e01020601090506010c14010501082125050102070b01050301051e1308130e0912 71
    0xa4000308030b6110b1060304d106180c0e91010380e08120b004141c443c1e40135203004da5501c0e020380f4029003005010b000d02c0c048445900907488400e1101c1c201c44c4503400c000c02086030505100d54604058000e803080308038040b8005807000c9526031440450866403400c2c14454404962015996250b1040c500a00704128965454401e01c50215041d8851741c081c4a551551210300001155100300c40400640072500030000000c1000b56140d9998100b540c20901c0303540710302c0c0425000c3c000030440a40a62050707008001903441c1c0b800c11402400040c2c505030402c401014610b0105600400c9954542d02d01d600014480d85071001c0b46d0705001c480b8043e00c0c00203a101c04c2340a00b0782d880e0400d882051105101c40b190074103075032500011004881d80024503c0d40046192401e0041070303c0098103c4001ba00244026031b920f03194442880d4144480000280100000c69441c10386d140326100302510444003a450180c6401c241700c0c0031100c940c0801040041031003003002101c1c0030700095000d41940082d0305c0c1009 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 762255215 1250 762253965 762253967
    0x7140d030908041a220f0b181e030d05030402040606051204060c02070f0905061503131e0503030f011d011809030903080c01151e05010c0822051f 64
    0x2100710704c6845600700240f1000d102d900707002000c452000d55403155040d10030008108080d40b900b001e1107513000c689188a000640807111800301e805000c4220a10107910406004200141217599006207802203880c42c01001a2010085a0390b40071042d11015140d15281c070420095072099004001003000038070111581d951200312042e085980a403020841c0954080c00300d00d40000c1350300000c030365186d192000a232645640d1002d401100240c40010007680500d04d00daa45100540352182d40e06000d4101401080000015440020b00080e440001ca0360a844192a503041513403e040103c0f16a001003080044030a140003d80d0400303100480703258900b032500e40340c050050380e442401075210801d0404042c4074454201c0510750007030505440e5003544010074002c0000f09842c3c1240c006000000c1080100c0c50041030410186111004404c0e01b840011169205103010880d0124800e000d1140782c5e040f031a50040207605c410b00c03a030086518040401c01010040300c1c00c0c2012407507040400c0c0c105 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 762256465 1250 762255215 762255217
    0x1e022715070f0f330608030a120b0a080718150303080c070c0b0c071202060a0c020d05010f0b100f080606090607050f0616050f0406180b07140d030908 66
    0x180c0e0b00203080900e1a04141411000d07100c2c07410004184484280401006144100c4400070a071040030248210712007011448048071140c0c0206483c030360041c00801562886014441c150f41480100424000e220700c0100b1162220f90f00405026041034005102110014001011b03110010700d0501821052080a504070402c0d808040c0030400311000080985105500300d603040d9610000b281d4001d95140c200100300d410030444241180603c510005001d00f2030a80c2c00074a41d0010a010f1030210381d00c80036161070162020491700600f41c109000c000c15404c0c0310341072075094040f0000c40c032415004200040c4007008000304003401840720b50702021507805000c1652010046c1d1305590b0f88c55200300091403901074000c000f0210711402d22960003803034010070345d24082d00c1d020034004c04d010800074095500340541248136141380070500007004000e22030080340c001d409112030f020400b41c0d140c000b600440d520030a400e9841003511007240803042c20411086044001500d010000006190f6881070f071 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 762257715 1250 762256465 762256477
    0x100c05070b040b0403110f0d0e060903071401030b030a0308010302180903070f0624261902041503050c0f03030a0c020d020402210a0509030306010c061e022715 70
    0x301005003c00a41018040c0100804685440d800c56265401210b100d554850840200380c0006040e5281c4485e18144030041c1c80041030014050500c031410701c20000301040c01d075071001d03040544449090030030b5203080c0110480c0c0c0d8083e9030750010541c1540144030b03c5c00400102c5518218888081015002005c4151410246e018248280141d6103052440207401084c9509070141301410842c0a030300c540380d04a408460005500e0354000940500d40100000760203980080c503041b56401a052510351402c101c50715100420000708802101c2c1c0c50110354055820465041d4002d190604041c80d114000d00582c2508400442c40c00b484036400410600000400a00440010b1104002c55072940c05940c405100c1121204124218440c1705021207420344002c4441440c020119a2005005c411a440340c00c5c10703140c02d1822101640c441c3c005210890b00240c032032607440c041c42d846c80650300007400b005c3c1000344a145440004070710031310386480980c1c92900c50b0b000740850600c01e0095400303540c4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 762258965 1250 762257715 762257723
    0x20a0201202b081608010e22120e03070b042601020a08010303110622020316090204060e010513030f05030708030a1d011e0e030c03030405100c05070b04 67
    0x1c81d602022a07480c0c9003030180040b07468491181c00008190340702280d007048120034560384000c59626002d28160201c03036a11aa00d000903218030050022812000f4003540002d680d40c91050b03100010402c064141c40c03110403c9920301c0c0078881c2200e4969100182c0001882e00700d001d002c000749426607408280c45a44505150b40c96006004500d0111811008074032410b910001d6648178400c200040081800b40000c401003003c0c0b203041d6800080c001025446207803552400070000542822515080e1140c100c01c99041c030517070740500b020a403085824030003081000380168645040030005446101c0c2a110681002024000f240103800b80c00c0202e002c4a401c54035104440000e820f040341588184203003e841050000700340f10b00010542c2c4122200c8029000396030610025038000c0703090359a1505c0094618503148039081480055074407103012500440203c03440c1244a0382803600f5904201c0e000d40d42070f00300407448034005c1c00c01d014281002d0301520708645041d0055030356030080c201c05400070b4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 762260215 1250 762258965 762259007
    0xf060a0c030f020f010f060801180c062a03030507080717060d0804050a08070f0b090f0906030f01060608040b0a0501051c0f1707200f120a020a030c080d020a0201 71
    0x4070b0003030b000f40300280c0a039a1a0009000d044040c0345102e018020138071500c41550b1034000641201d01c038941004100d154045d0480c049545000341c219150340602d0f5003504422035175180840291400500c01c10b615100b0703100420700345413024000c0c14028006141d0424406c02902c60b19814514a4100351b101e901210100300c011000d062080035805242c10040d0080c0424202240d61280000c40030b044566090304d503411140c07240007240c1540a15190503411690000360901d444c0307040da8001c1c0d8440805011561a8000360314400c0c20341e030143c1e1007400402e140c0028841440003c020031130380031203500002d21007540750501140318420070f480400040c0100341d00010420803511103049481d07403c490300d00c031a208418800d0074240d00107001241d0201c3c0303903440300074003020403511800454030007888507401152030000d200c0380c000c0c0d43c20512907074010380c801d00d80141e8a0100907400307103003da2035412100381001e1640c2d00d400c5202082c40299840307511000c00507a84020f4a04006183d20100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 762261465 1250 762260215 762260237
    0xc080f090706210507050408010c091404020307110d11300f1215040b19050609060705010c0807020708160b0c16060f0e09010f0b0a020f030a030b0f060a0c03 69
    0x7010009224180d000d80ea505010178040c0c050fa010020300140c0f10307000002c00c0f003002e5809050768150b10920807624070315030a9105038218500b950203942c0c03065442c01c101c00010540141242000580050700c0c020a084400740c084c081810040e280812180d0349401211070750041c0790101100385c000c1c220144081c0012000c3c10560440e05840c0700440d10040110b05d411304005d4403219400405000740283d00d40300f0306907018039100410100309401c42e00115540d6040106000b0740350700036034410b508518108401c0780005d0f02440b5101881c6055a540451420146402400c1000e1540003200039800510840300349042610340380129807503541ca00d81e8078284c03d00c20138200720290144280c0150212030004031a9004082c9803003402e403550700c2802c440300c540100015240c0a028411842c0405602072100c012000020001c000c03403030045406a484030b03401c45255a01c0380d441000040d072a1300e0305c411181070400c40e22624500888442d03040c00c1c40d4480040442141200103010030008800c5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 762262715 1250 762261465 762261497
    0x312040503070803091c031505130b0901120c05090405030904020703031404050a0203010e0d0221121e1602032a150117010c0c170f0d0c080f090706 65
    0x8582d0b5081d8407460690316850702804081e16048003801816192440e80c580381079a603c613104024104042c1c0001e401300c282031000307004002d118005013003900340d600c108040c0165a00a1003d00802c502d20040860009900e02009a69090f81c000b40c02401c14006100020f00c0c0402940d03008203041d41e0040e203c40300c500b002c4014052141b54500e10b41201401d00c01840360110b10070030709038000c1d002400000034a014561f07075090105000c0b40160003001c010a41001c2020004920b105508216428000003001c031020001c4207440000552066001201d51003044172159680100c0408040b80e0105100c180a503e03032107141ca4511810ba140b143c0c4032803124454484100e0058044110b81240904448180c1c50103828051441c2090050b440040301c80d80502510240d00c5441d51010035510499070703410303444524400d90500f9040e06102010561300d4210180420100040020510242c0030b0005080c41034080c00860052041c2c408100080000140c0903084501030315140340c14040b0f00b02 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 762263965 1250 762262715 762262717
    0x71202090405010920090f01050c030d14070e06072003070f150e03010b0607080c1005070c1e0201090b09040f0f0207050607111011070611040f0b07050312040503 71
    0x150300c10301d010001314a00300305500ca1910184014043c031010901c0311442d0303405000341c0c1d00c082d610000c80c0c81c080340c040d4416000f81c803414501c081104c0c100f00412801ca02070b10108801c0d28141c0450b04100880d03590300510349440480e003517940d50b14083c155103a462403946008481c85c1e61502100030004140c42c00c001500051107005009205180c980180c0480d280b2038840030000034042d15400740180c60b040c411000c0100c4000c1c00e0a00c3c04c1c52654601015801164903000c081c040d9524900380312402e4050144240210303078602e1000a230314500303d81410b00400c00d052120b040c0182460041c0d0300003014005a60103000401e403250205030000d0094010a0911480542003204c00c44604140d6009042214802c8040e01c9603030b51609000c581c800c00b0400390300c12680c0b205c812070115940c1a4802c25101c03540c10300d0607183c0003440e250703071007503d0908440c1000801e00290420a140007803034004050141901c103240360411546138503940b070046086001c92080071002040c20401d00300 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 762265215 1250 762263965 762263977
    0x330c0c150d061d0a0b030f010c08060108010e060a090e0304030204151a1e031e1305010b150d0c1b0807110f030a12051314030c0612071202 61
    0x3050000c8086140e0004811904526060344070300c1d040550224251200300034107603c0c941903800c40641641c4030030380903000d003d80304c4105c3c6d014000c141d04450203d00030700802034030101544801030241009000140300c8001680800711022180d020321505540f140c1e20b0700c089a40c1004042020f40410365064218441c0d80c1c4001e50143c0f07407010306040c0340300c46c881c6801183d011000300e448210348104420a14414440c1b1010781c5035181110030b401070b0f80c2d8030145802664507000b03200e09240c00714400140c0b90701503504403005410343c40000204030090050540044c2e05450f02e03a000e626040040e42d0700d0041c01503241b01aa10351500382003c0e88500380740044214002c29071015000c4c6401c220307103681d00c0503c05071418000702409001608008011041502002d4000c00b0f6803500c644071001c400b1074056504040001c10020b500284201c0d2281c44c0244c804040c1d154003603113011041616200c50320100a004520601014004203d041449640403846003440100440900b044c40c1c000d2044c5c2c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 762266465 1250 762265215 762265219
    0x61e0102120a0905040f0e0a0305031e09010f0e0708150405010e0607112514040b030610140a030803010e0a060504060b03010e0f040b0c07021201060e06330c0c 70
    0x316181849561000080f0100c0e04196010041c1c07200542da4402602d06594460b540780d0701c10303048040081c2c401c80041d64000d074001c209141c450b592a010120201c0180d0b82003030340c6d0391292552140846144242c422950600f802080d003d0b140801c881e4445000300d500310002e81e4940d0004007448402c2d0843d0314082e050209992084c80d20000107020700000c81d0140200d0300c200000c0c1d400303951581c03222110108860421409142c83d010008006110787c0c2901e41d00030781c50304040c481a840c100b05050083d1140722011781c10b00d091440d0110046c0e40300d80d90510480e5203210400204410b2011641510f20340c0710190400da840080500c080c0c5025880b13103820a203040320000e00c01941c81e0246060300c81402c0d407002035442c0d450300c0c1c0c100a202650f018010000100c003040b02d91726540300904000c7c0c40982801544101e0a40c06400c5840543c00360032082d40000c00c0213828a400c2005109010002d1001104a001d030340d070040300c00a020003501c03060f4500060300c0500100400c0a100707c0c200c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 762267715 1250 762266465 762266467
    0x30f03110d0e060420011e02150c03240f090403020708100c0906020102031005010509030709060902090f030a0f020f060f03071206050a0503060c0a11030304080a08070305061e010212 80
    0x148020b043c1d48100c101c905540010310081124103803030a8404100c003000050b0741b00d03500d0039491b445507820070041e503000205520440b52000c0600b40807281d00c51049030361020f655140d240007060300d41c544107440e5070781c82035280034100a4070664036641c941190321012b0725407030343d55030341d82c80c06a01d82140c40d00060351601c145181000c4401440e04824120100307681d594095550740c1100f6401d07400146d48040c00c0c41131000083c0300c0d03540f040f80a0421070200600315480d55a0303803030904044070482e402100d4000d400003032011a44c01c220180d078181c880b086d4000d027144042601c0d19008000e610300001d10410f42070f40403203c15526802904c0410301d10080e940e40c1e80c1045400a803012004444010040341804000555450840b4000d4110340c405030192440f270b95421451061984241d40c03040500c45e512641c010810010005544503070300c111081c42e5607a00c210000b50030150020305042c10581440104842e51b26404d55414104c1110400e103c9a4019480140d0a0100c039040710350403044 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 762268965 1250 762267715 762267731
    0x20c100209030304032a12030c060e010213080f0105090a02091503071a070c0503030415030b0604080a03090603050a0b0d0303091106221e06050a050c0d0906031404030f03110d 77
    0x7910b20700420003003501d01c240321b40c1c00b655440085002c1048400c040c0c0072445420b14031011409542009003c40c540c2e000061404440c40c03c13035180e41c2d029400585256016825406a05500344a8543c00030351150003442c1c2d261380c5500003908110f00620140d4907010b40c0024100907203040207100041c082501c004000f00e04007412036800da4000800907a40c20044010009040c00c0c08811a02a01c85406a40c5244a250241600a05030180090b42c1002c003c200c0010100800d00420200318840c0e41d070318030650700c0c0c942d0007410307290081c14a0203c540341814205e0103944401030f04141c6a40b500303012407825450308150401c810080c1c0b020b41c0080f0002410780145203541200c0c900c1200481e29404502c0e1940c4180101460781b061944181c6100303030090164a01440141803204440d251103441c02c03e00c2012581054000c80c600c20100d403214100748030042c2c150140e150120b914490f141701515103910b00424444107511084145999000d6081e0305003a00c07011a001072030715440602144d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 762270215 1250 762268965 762269003
    0x50a020601082d03160f111518010c0b0f011e1401030c050d0e010f0f0b030a0201181a0a080106021501030b1008061305010c0908070b21100810020c10020903030403 72
    0x5030f444a01187e010750074a40308000c6240c555440208044c21819a6081101d688042251003400c4075503103061200c8015034200055146000300d21031035451241d08103c2d49030950b0001d1030122101c1c4400300508060051110800011210310808002d00c0c0c045a500f140800503031341032040c2201d000000d03080000c1094155815000740303100c0703110102e080001116541030307a4100d40360003040c2036154004552250256100760840c440c51305201030b6a01c115650f0705171030201c0b60110030821441d02801701ea030407502504884a43e004099500280849102400c029144000705000060903041d4141c0416003082c00c1000101c06400c050040781c00d203040c46000c205c1035070340e19441240c203582024a04a00c051051648408803507000d00100720301400c01c0c0d8501200d4219161450120040c14100e116014544aa060095140d808080c480f00d041c50038050420b10000f0040c0c0700c490042108101e02c1d8030014040c004104e140f000141c442d41702d10002403c41c842e5a001601c08443e0081701500380c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 762271465 1250 762270215 762270233
    0x30b03010513021c2a180b01021501030b04031d1e0301050a060e0a09020303250c0b0418020c0705030f06010e09060c0a05030a0b0a06050a020601082d0316 68
    0x200f0b000725401e07261002c1e4207218508444040030000c00b1250f000c98082c0400c000f00c61a0300c1818075500204524030b4840d0a00c40c00001c502d01d503034040c1c544451522800703503014001492105000401840303c0c0d81503480e403496484015000508121105c0c019400f040c503401701d203501d00540205044515040b0400d5649684124810f0600c25464040840c0111078544140c408443c54082c070103410360b6943d20303480300a0070080b2042c0e8041c04100300030740f065082882001c01c03044101d22031841c1004c4500b4614281e82c01074004c080302c0320042205028070070012606800c8200e00402c0565a44258980103041500316070005030144a041c2485220800101d8020306a8400b6070008400b0f54034006669940c04040d03c016007110320030000352214038404c0d00116408225800e01282050004000c200c0c5261603502c8440001d00124020032525414000c4500500115008001c448030741111034258415191620340306900d06040074580c16014816910201d00c04d03211448202c100341821510 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 762272715 1250 762271465 762271501
    0x906063615080a201c230912030a110906040603020a08091204030609030302120a1b020c090c1605070f090c0201021207050f1b15070f050d020a030b030105 68
    0x4034590100182411020b48150044a51841c96070740c8040a4559081c545600543ca4840a00b2500005c0e001c0308021b8020706c02d02424000076034000c82200b20010a02881c007808520050f0041c06414124001003002da036004100000c002a207030102950740123003881032110640e000680030400146464150380500540e500988410680390345400e810340d241c44c19007021078035440c0c0910041c004600c0680c07010803564800e040045c54034006d00c5101d03e58060449060500c5505d8000051070040a00c615101d07100c0d20740000c4c0450b0421400241041100400ca0120903202007056070144c8171054940201d240c00ca01603450194a841c440d8482c1c200b64003035111002c2c101801004440d105100f1201500c56010610b65a038039041070483d4240e01203a0102007086040c011040c5444200000c0301c4d80d00c400e0402007800c612105164000034500030071200078044a0b201004030790381c101048403d40286004010f903100144141a0001c20350b80d881c0582640c0381038104501c0305601034002d64 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 762273965 1250 762272715 762272717
    0x918090605040b060a0f060504060509060c1009020f0111060f04020102011d06090d0c0b0a0c090b040b09130e03250f0f02042004090f020c060c0d060906063615 70
    0x100290300c800717111003034034111f00ca0b8900007041000700f040624410b10141c00ac80310b004000724276011040300098a090524415002140d40e0341c4802011442e2561000c450210300303080540c1d4281d40014008c1d211800204410300e4180b0200014046a20039400154403913140b1fa1003811443d000108280c0d1001c04540718000b41c480c58555645050194000490050f032220480a440e80c4150042014040041d4050107010002c00d01244418602018001600702e9801d16612442d8500800c01040c080c848020076080c90056031400d42c20010040380d035061240411140182c45460a183d8020b40b00312014051494020003d000c2102440c0718843c6c85000302c8041c001c60740305507404003070075a06800e060709441d4104010465040317241c02c004026030600c0710060810619001d01410000304460b00303501c8060000d1454024403240c03180d20090302c07880340e041000342d04083c00500403407003110f8a424480202082a02c06400340060400300c9803c901d110392001e5907946148c08601a08003280c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 762275215 1250 762273965 762273979
    0xc0e100902070c030609050f01020406171617040828110f1e15070f171302010302070f060e01050a140c0307050c1603050c010314070918090605040b06 66
    0x3909180070700907100ba054004000780e0159103540e488400818110342d04450b18050720782201d0080c2400e2018000070280d039216683c1c20401e100000d0420341d03000702840e40e0001e840315156000d0742d20200404010311221a054465151414607035204d000b074003074801900d5801001c00540e8001380080400000e19602c03815541c0c0004940d0b1a105c0070700d070051240e0f80e40407844005400c01101110303940600160f040d145005001003030300c0d03c004012508403011528461010000c0c81d80087c0410841d0f154101c00e01c4141860039810300380c00e09480010b0304058011541a05001d42d50b2140719210f944244100f096840741c404c10743c041c2404a0b804d22705185468545140d080d041c3d07084a00c10403014005074510780c2d5000c419962a0401080c0601c0382c4501180702242c00340715803c000145000d00024000e8840b408001400c1d41c0d100d42082008070100750601024540010703e2109517005c412000c0c1340300d0041c1d16040006c003400640980240d0501042c0001d01401d07001c954001d24040d01c04e4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 762276465 1250 762275215 762275219
    0x60c09030f060f1d06072312010e0606030f060d1a0a0b04050a020a090909140d09030b01060f020316031101110306090108070302130510050a030501021305090c071403070c0e10 77
    0x200b100500c030881c0041325810003070005110742d01c00c820341502015159004501c00300d1004510341319401c403800d811028203c001c014031410b045071180f079a101e201161094514580000022252000034014a01030050f860806081001c0304550542c4866160344004080c5010038510000d40021000c47d4080c902e0000130a01140c164002c990b4901c1d001d480b440751880c50205c0340801410051401da643d002c030f4090000000340103200302c5171008926a1109400fa00b5428000d45402040e0701078401c0c492542c101008041d00482510456040101032402d008214101500c503800d1400f01124503519207507a808000c1715403000340d4018001955942c94980c1c98a03080c1c1d955400c9804041d500035000c050000900c0c03a240c01c5079a0100024550040d20303990f4201051030b076076403608100e031076940106d00180f0b0441042e2080e13005080454041000d800c244003404464880c114029100c584002c41c060404034041040321200d41c0d000b0304034100c032640c413045c1c2035040b04155501c0d110082404c0c00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 762277715 1250 762276465 762276491
    0x5060301060605090904021309051005070c0b0c0a020f060a090c090b030a020d0f020612040204140c030703020a03110a020706022505130b100f09120f060c09030f060f 73
    0x75250584040b52515407030001c3c00320400004484c0184100d0380100f0340c0d1214448400103006404a591040c0020045601c01e28412415101c0040c80e580411091050700c07004030f44100b100981001618144c10b5030340b0406d8504a04101440361048a070b0b01c242024400355104e04e9100c1002c07140035002c81d0541da503da00722030301500c10120166a140c4e201c80079000152070100081c001180c403920031030444210982c041142e6400070903c0c4e2000d10702260803c41581098001d60305049007200c5184007514042c0c240400f00e000140051040540c04165031954501030307031103001284e000c001515210480c801000356900164014075006016000c09422a1440c40031510070500020140c00092810300040c0554400900000f20745e0940320403085c90161240c08041c840c11130680ea0f00f00382803100442c09000040c0320b0b4018a0030343c07040060079011503001e0f07103102a0f59a100e000814500e0380c098007240d81d01041e4101621601120800c0401c0040b075a02c00d030900f00c80880c05000950748140 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 762278965 1250 762277715 762277721
    0x503010203090d082809060b0f0a1523040302010906020f0307110a090510030605090d020c0603060102011b03090c0906440618030c1e0304170d0305060301 68
    0x18910159a00003060b414109010314103140e800704081190f00700e1401c079061740107980718451101003040741c2d44480500030321055008450344020103031909200400b0f01800300f15000b40900c944180e03429400f000d080d4144c800e1039100702d56610003103400007058402840001d10b0784039110480c081440f2541c0021940e00114100d01c0115040c006941090a9501c991600300307890011554400940c81c1c0c00708100906d8420703076018102d0700c0003c46e152403c41c50b0a00864801400c410a6640001054164641d0000f44900043d00603501248c1b2074403030f800141d014060303c902310400f0400d005d21580b4050b03810750020f04914040c1c1c40c0002031079511260442103038900e010703855900889039021015846602c0d080c2010780c940d42c04144d1014400b03d1080d100c0e05020107a01d410360090020b1150250384500c1030301031700c0c2121002d180341a80c1403081c20743c1c0301201c0740e0740181c0c100a40c0070880d2805007441550006d2401d042205240e002180354552541105000f0401081c500004a21329041c144 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 762280215 1250 762278965 762278971
    0x9060f0306011503021b030a02010c0809030906070807081b060106030504020d0308041a0a09030815211507260601120b060705030f0a08010b070804090506040b090403020708070503010203 82
    0x10300601880e900b48680d42198040c148400303420701d5020040c1c0100070031013913070903460030002001564840034030900003070a4440c40b59452041150400a1002e070402c044210f40048108030703840d90b650840c078a440302d058020b4007000340c22408003003018240d011038082c45103459000481038030004c4c2e8035031505400701c8106803006034100d0b44503442e0300000b80c060100c25030460701401c82c102e621002c000100d44016811544602d010b601c80024904064010403030359000311110f08059001c40301c20000c904450201102c18203117110010036a690f80c1c2d414481054190704014465200d0314080e036015140442c408071003014070010030801c03420030b01100f80050081a05a4595603406541c15042020f0803050910f00d0740321750204034070400150200010302500c00502c1c07060317446d20011316018196100c16401034149010401c5400001456101200e09a40f07000e10002055268280400c0c024400042d501c0e80226801003440185034000400c0400c0300c56000c12541a103844000340b500382c0c001a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 762281465 1250 762280215 762280219
    0xc08030a09060f05131403010e010216031b1709090610020c10031d0a11030d05040b0a0504091e050703090b04060c050f04060305010e0112021f18031109060f 69
    0x292420b001051044248440b41009850700d6401c14a441a108030003510f154000440d1661303803460203120341402e003e0f000600c04010021414589204080b00c410110294000c08100022203aa510840104040340c80b40743c00c1000341288465a02c460361207544003284036881001201c0010302c03503180056546150070304c2940545003841c4440144040171220040d20030034552510074688411849503552020030848070000c2408140504107013518201d000ca0b181c1c06a001100108000b5801c10107d8003103407045a8001c1d5100d0780c2c1402115a4042c68000d4070105041640c5103204094810610840f1000b40004000d242c845a10507000c03140075080041185c80130800103400300e5583c0e8040c0b0f100e01c0d038504103286806000a000943c0381d020703822010209559000601082000140460241003420351080d1004001e4002500005005004403001d80c01500301d00307442446a20300b4901e0451141d420701c0120f450b1300e0190003d0000400d114000c0225034005980c0d4500380d00346900e59980 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 762282715 1250 762281465 762281477
    0x151305010308160809060d0914152a180a150e120a0204020f03010e07090f4115090a0e0903091008010303020606090f0a020a02120f03040c08030a 64
    0x20301c0300c1c50f000c081020b039001c1d0b640100070b101c0140152106801032140f02880311000a041e010742c075124040008040301100e065001302c8030300d2010411007617041d4020000c01882c9001c00b10701e00181c07200800703040b011480d0f01004507500c0110b42d501c034014069080103d03144041c0c551a1040200e004005900e910f0001d8998038800c1c40d5424a4400c41d41c20805200c25201880341607004541aa032240840460550000004100c4900707a95500740e0413070410300e801c20340703d46030503010002c0d5900c60017a0401c000c88036204004a5074100b546191400001d03006940c248100309002c20b43d000040e0113940a02402414031020039841000c4801e400d40081401c132009080501c81c0702c0000c801010200390381720400040402c0e641d5160b04109010090303a41c0d003465030451070b000b03042c080050325042c0039413184014400102c4051008560041c01e07a100142c42d4403a82c80300702d20f050b44028a1800c00c0100003065032051925130000c41c402c500440c8a100c0d19070b83e400d1450350324801d0400c02c50000e01 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 762283965 1250 762282715 762282727
    0xf14011a1315050d1b020303060f1522083903070e07030b040b10030c051303110f03010203040f140a0b1501081b03150d061503110117270303151305010308 68
    0xc1c1c003901c6412b28041c058030300d681e01c10101c101d0280907440168442421070013980207180106032954050064072500020b001030508101c1408542c00002041030748107000c000e10f1410007402c01c1c1c2c0c122041900102151000e0f03a58101e03040602030160741000010781440034402c5603042a010f00d00000c0405040b081c60415494811002024440c103240d01304182004841403103c503c2d0320101c06140540030304030300d4884040c100714010708c001c150741d4042e90040c01040301280054400c0501d95170043c0c00118141754151019050032501d4200400c1c1c41c02000c2441900c0c803015194618002d420789901c2c1c100c0d00c0e42400c010040b0401c101303030300088204000141419641003817030000c1c00005008103000b8070940e582c2100b614811081c003011400143c1041090101030074030f43c2d14420080c2456240440090030070494110000e1440d042c50108520303042d8001c0205207a01d58014581007929220700301000011040c0e0040102c0c5d61045510356030816200705148103080c1201d601001c0a45005 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 762285215 1250 762283965 762283969
    0xd1d040b091801061a0a08220b22030504051c08040b0c01060b0f221202010305060622084c020d0f14011a1315050d1b02030306 56
    0x540c04401580065488100020301740c90541007900941c81c1140c1e9880c0c40704601800142900801401d18000305058070380c0c010780c49110f100c0b005680e504005003451340d580e00103402000f40c240422182504251421075002c0c50750180282c010b07a94100e0301002c1000d40d10781a50342c52601141c004d402e2aa0800040100d110900010700310303080604d00204415a4409035184c8036048140340a0403c8400200c590143d04500b83c41c00403d00c0005030280c6d00e0341020f481e00c140303850908000781410f42c0c9a0110741659070781c4c020f0b69413010103213241c500456101040001d4000712403003009224810781507165141c2000b10030000c15000c0c1c040381030b20180840b003010810a02e03540a05201d1410102036405000c4107400201401032200c03c020506215078105e140c103e41c03411401d409015001d0005200311002a100005000302104c48652548580a0310700d040112a501410181c06a051000c01d00d68003c03024040300c1260100820507200300e000540d08640000c44c482d00180c10410001c1c02034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 762286465 1250 762285215 762285241
    0x2060a080702011b080115030615180b0c070f1706070e0117070305090c01050c0a021026040201121a12120f03090c03070f060804020409050d1d040b09 66
    0x80c40046045100d90b4504014424600c002c0400914180014019095a200050740d904003501d400c020180c60803215503801031922b04100200018100700006400d076480440003d000c2c0304558079030352404144c40c1980c0d08054402d180e1240b04008000511003070481407034082c1c00c80d0001510803a43d800301c040315030a0603188024180054101501149500090214480c06068030001a41e003400b80ca01481c215860103000d0412808003c10320005801003921440b155056136903041c60606d00400340c4507852260381421110301402d418680f15000d02d06e025011740e00030780301c01060f140b0025109041c2c90ba411031507403100b040d0141c1c0da2290f080c00040e485050749040b094441719a5600c40c03118980c0d00441c02140c0c002008828000549000e028480442c0000c80090007007a140540400c2d035006588600303018400500000f42c05d540300d503040505403680c800140c038000c014507080a003e0305010004900c0390b0410800e9003105040038802c40c0700b0407000030581081d0747e94100c104629 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 762287715 1250 762286465 762286471
    0x60f080a0914030310081b01020714030a151b03051302210d081803040806130809042c01060810360303050a050606040b0d0e16030614010302060a08 65
    0x10542c0c00c0010700c10001824405540a0030002180710001803402125900d0101058405880e10b00322a042d0314460f83c001030340c1c1044411004847c0b1610484c000000d0601c0d84642001d01440070a1550480060150380107048044928000b44002c2c980408210105c41d001c5813500820041821582e0140c9880340441c0304a0300c100802500307640e99100f0182c1031240e1240d5900209403541c09000760a2038100c04a02ea9407100ba0003581802e2601c0002a62008050102d6004080d20009441072006500031244d00040190040c005001030380e4040603200c130410f81654125001181c3c4c02451039040c000c0400301e8040e14010480700c8500781c26500207241d82070b2100324070b42d0085400f04100f04035018814200009004440003441c242c00c0103400da40e4024480f00f4030394500b5081140303d0fa11172081e50191007594504035120420718210300002c0003c0050340c0c01c1c610880c0078000c1019459040b4200352442140140321000c0407088a80c03001000b80002940030805001d107026661054151540c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 762288965 1250 762287715 762287723
    0x30e01080603011d07030308061e090711071508130507061b0609060b03060c03070c170d1e060b0906070326090a1202061506181504030507060f080a09 66
    0x16031480c0c2d0400604280300540c80540545c5c0210f1000c1050503082207040354440710a486003c03107444420b403d500e021411a403218420f400ca0070104a1940c4909402000000203c0465501c01d48030710382280e100f03101404007000512041c0016445c005d004160b00b2172a44e01500070080103040c18810b80d1100600c520a8450308c1d078881000c001310700c0d11300440860764080c0600045000790302081c1420000300900d02d002204040041c022029403001500e1310690300a500640f442030000f4040d092407180825496403982070119101c0d0b0740404070480700078107030410010020249d803146a00703a0380c0221110154407031028006800402c1c0144841e0300558041c0d0f14110300043ca211000d1492a02904c1c4549281c0c0a442c480b4100300212816290012260004041a142000d03c041c010002c041a55000e840041290518885107007030080702e6007001020b04554582450411420307410511080d50940300e011000070b1034a02a1082e00c000c4c2d40181e4071440d06903a800c0f21440070306482c0604403 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 762290215 1250 762288965 762288971
    0x13080a02090c090126010603050f0c09091e040506010e060a1404020c0312040c0e0604180f0201030e07060c0b0705190c0305071707050c060a1d0a0816030b1003030e0108060301 77
    0x4012020b8200c0d8817076800c80399200103294180240101110402410f2400203110f12080c800e40f01c1c50b14090310040f0000701c031480c000341d0343d0030941010007012529040c0105102c2041c041003060116680307045c0d03080b0303d5281006a4a00040005070002ca200310440341c1801840c8005a04094000b403580d034001c04102c920702800701500d80542c1508603016a0030310342100303050103803101042c0d699422100846040c404003450225106403c0c135114070091040100c0d03440d9004590003504141480d14092058810950361540090404041d02c081200d5411009001070003607401031050f034204004040340c5100502280c281600c20a0200c002034061202c103100b550700045041c3c040551060f01c00e2400c41e200d554900d0070301c0c030f024800d40c1c01d50312070315051018a003030f030703078040c2002c80c50451039400742045135200004280c00e12904c3c0c100f00a01c1c000e1000154090100d01d07113540441703225506010499592100d003180202c0c81d40801400945600c0c2581c040d0341c450360380c0b240c1000c4014000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 762291465 1250 762290215 762290237
    0x30a020306071107050103021321020603090f160806040209130503161b030305031b0c030705010902011e0e0402071407080c03150c072301050c13080a02090c0901 71
    0x1e2624004841c01e40004510b0785075074200350810f12070314004003802c2c00d0035828502c0249514038004114003400d40344070b80e01c00140c008008000c0508080f181c000c1e20407a540d0030102040723a22a010664080507510840340f03000c10383c614560a24080716080030250a507a212542000102140580002d454002e042d100380301091090000744106021802c84212130284c0b403030a15499407510101156803010800d040000c241c015040300d07800644091660301600300c20040b103045000300035140e1003031710000c195042080700550050071081d000341c880b11900c10649040c0041d545607120350700b0000d41d103512944a02e00713180d00605000c91150285448610b03c0c081480e24020a41d40b00011545c807007124280c01d418140015411585c030580e0750262803510b0804450144240103004009554094081c1d142d04840a01004048031220080c000360508101c81ca810b0b070030401440300e5690003147c00140d903200001d08152403c1e4050451803540d81d0759622200b041c0c1000e05c00c203042c00120025 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 762292715 1250 762291465 762291469
    0x30103110409390b032514190305011e030602090d021009030c0f0e060d03020304050a1205060604090b06130605060a08040506010f0b1b070b03041a1b09090402030a02 73
    0x24031001d800078000003c03800320b210300404181c900c040e8080003050f03008009000c41507081c0042c14004007141c61022201a000290485070080402c0b40d0100307220001c1210717400c2400044100076040c009640620030f607620b034116030046980d0203480020060b101d2400304002a002e8001c1c10480c40c000301800041a5950045806038035014850720020300c0c409001d104114030001803101900c0c82e1010020b0a0f42048138000c1d071584d004d4801842003031503074182c80425100700200c1e4081e040242000381a01e80d00d480c994045641a01c00315450b000705030001d02682450700c00c0075a0f590b0412103880d00c0c0d803660410310501d40c0d80e501100c0c1d82140c0340d00c4040b03083c3c3ca81200420b044c0c51140c4d202a42ca107000c3c20054204001a088070000d581804020000c130386807002500c40b0748031004c0c15101c0d030201e079103041450080242d001c203010650200400041c0f0190f40b42c5404e112004031120901d507521802025000000305940d100c5030304040c05080c02c5410184c003c190b0203440682150004041e03900 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 762293965 1250 762292715 762292763
    0x1080706023c0307021f21110c06010611031c0902040b100c0605011d06060309070e010609030312060f090e19050109031d0d03050c01180c1a030103110409 68
    0x4040803254000a031313000860034100440026441d80d601841e00380000108010f03c0e0071a1000020050051011003942d600055404904a44e001964a80d59000001211926203200348151804a9054030780c0c41010b543c00f00480d42303481211035003011001503540d4003000400755290140d0f0000d54504088589855210300b240e0324829a44801c003042401c0d2400f80d0a80d41e050300551454a032148045094100c000146604801c0442d0b045481e079031001c008a240c40c2165212001214062000084a517040140001941e010799107106070200c0d40940d4509440c0305c0d10404010300c0c00c440b41000f080e5200d40c0f00d500f40180c0d00d01910b1044101c0c20003480b03c421900c10644459560f03021490804d03402a5810151a02c03030400c910814007030000050070a542040043c017444000241119004002c3d03004000c13038004450702d510741c101079040c0001c091049002d44c40c0205644205503103205001c00680e8103d80d80a01c014400e0384a0724103100140000031800c44100d45032202e042044084a1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 762295215 1250 762293965 762294073
    0x1505120106030618090b180f01060605070c0608131502120a020d05010e01080c100306030f061a04021315030b150304020109060804030f08072304050301050108070602 73
    0x307540032500e5418112403040c240084c10b000e404070307440c100220340000e8010010384d6000c411248400d51104040303940c3ea04000400780c50f0501c55180c581c010a038250445c4c0070700440c0d0f00460cc281101034440344107640491b0103903203000da46508460301000241002c2c010324100001303a03a0142c00c0807100c1c0c036110007a410589840c5140e075000308a81091482d50720550b401045072130840c94855161002c0da60310b500c2c0c16030025015140680345104014003907003260b0000c5174003030680118074441c1d04041008100303ca00044411070110301555851406000391022500c1081412039030310314043c207494401c45509520014582c860050080f907903030741644801000c0304004695543d00d0a440018a003203041c0d000380303050103480028800804c0c0c0c02400070703003083c4d400d04220380c1d1500d40b01025070b0354002c0c1003991603070003075030001100300c0c01ea415019104a40c030940081c81240d0300c6a6000b901c40c0110300072040141e1191860282c4080e9407008400e00d075000c00502000c0d01e09c4032514001c820604 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 762296465 1250 762295215 762295217
    0xc121101022703060c0d05040206040509090114010f05010f051b0a030903060501090515040f240303080c1e1b1603050c010c0b18100612120311041505120106 69
    0x41007103208003010070100c2d444200085000c0c14207880e1242c0742c100c0c03034000e100c00c10560a41d5180010115219030040701c0c041c0a00038400e104500e01048001c0c00703008440300c00070041c00040000140f100c2d01401d0b8000340d4505031519071140600c040215919040001c81900441040b801c0195100091002c40045406555401e41890440c200442901c006038001002c25152a00700500300b09100c20b1103048010881c3c000c100c40d450890352402820500c40654500f41c250b101481d0180303810400042141e00c262645d1017690788080c494042ca0040c0b0f141c80100303900b000e01009035009042c1c010800100c4401400c8500c90200c2015890800501c01d40c0b90a84030001060090140800444a1082e02480c000c071800c0355668450001400c0a0a8000c5404842032690303420102804501f10920600c201004280e54402802090405010064600880100c10312411621074000e407680c60b096079008514061421810303000c44e00303150049404212040c050902001d8002146a000f0041 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 762297715 1250 762296465 762296497
    0x1809060303020c03120906091507060f0218010c02060a03021b06091605093702030f040218040b011401090b0a020c01020705240702010e1908100b010c12110102 70
    0xa0fa0080c546410026650141001c5003480701c4190740d51040115119a04140d0304106902e001151440941c000d124000b0201420404a1142d45900c0e6000d00b007208941c1f080b0300050204440103603189003603401d001c0d400080411079404141d00903002891921441c0b130815805901240020341014001d54581039540c1106601d03050595004126a01030003040f01d2450250620640100d60b101705214501c480b03d80400080f054200781c81414550006000700c01e568916040c44580c010074811503040740720b020840440d040b000d44401c401c500c02d903445085402c540e401c103190300c645404e003009007904100b9950404030761620020040c010f000e0442d0010140b50308a0400681440810b402c080d000d0041c1000fa6500f0480c05400d2402d501384443c031940c0d0340e0015000403944a01c0d0f25071b48a070015082c030303440d0b5440c0e01d020041030119101d02c403c1d15140c1150350340b24020b0f156000113450014085a1242021984003042082281058100035040d40c285d8a070203400c2e40c1045910001c8100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 762298965 1250 762297715 762297733
    0xf09090108010213090606080604051b04060207052b060e1e0606030c0f031002090409061b09060e0d0201120f061d0f040b011a13090603060e1b01180906030302 70
    0x2581429884c0640174003002070202c40d04000c00180b20b407034018045440745803920301148210040ca401c2d4820f44c87d126002076580d5455140103551418244203203400390100280c0ca503a007600810b40716400180d01c10001820f003400361070f1500a8500c4071100545401900f0300c03440c2403032540300301d0003d0401c0303100544014a00f0360101130500b00442c401600404221920728040c1e41d010403084c1149a06002c0181c88081c00b601150041c030310540010200c618041003030300307501042448816100855542c00941903290360003200c000ba404c00c96143c1002c51411010010760041002c40c030450031968000030200c0c03940d45218166043c55225158000760301d24505804183c0c40b80301c0b540600005d0200ca15828699600798850718144a020a92030b00d15103a4541d1490340070465207842101c828405100b40c459480d80e00600c070038403084914a1030000385405841000c513105d403c0180ca1000030300c4010156005594049806540100c41d407410840450800359501c40d01c000355000741d0081c95454 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 762300215 1250 762298965 762298987
    0x6090312020c0a03061d06060303090415050a0308040f06020a03090608040312050109062c06090405190c05040e0a03080a0b060c01110c0c010206040f030507080d0f0c0e100e04020f090901080102 85
    0x1e64401d5051b50355081030f0200031082c2c030000229410000c054800280500ca002001d07084820b0540001d540000014000014000e0b000045d04c05c4c0c2d40346020220b0110ba540c00266614061840010081841d6030300c2000383e2400382d400554000c1c002d08084038801c1031004c45c4c0c421075509800121145075a40024800144041290741c1071020200c42c0b4032190f0203007103c00d003201000410080c4501c80e4500050200142440480c69540c801c81d5042800000d51400780c80703101003030040038020340c641203ca614140002441074140c40e010740b40d03046036850700c1100c900a00746130f44000d5000f00b02005920701c4103100344140194080c0300c450540d1251030300381c0301c0303030909080c007086904650107081404003040d00c00c0c15603000d5a074181465507031042149041c5034507024440e14444400e14001440911f448590482403400203550f941143c5000c3c80c9041101045501c40c1e1000040c00000e100e14030343c1056030041c0120010f04d0b000034240308100300003800c5140300b42c0004415940108003281b43d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 762301465 1250 762300215 762300251
    0xd061b0c030306060518090705040b07080403050d0f0f18120f11040501080303070e0d0b0708150603070914060c0a120e040513021e150901120606090312020c0a0306 72
    0xd444c40f4a041031600310b50949914004070f1402e03880c1c0c0304558810118913030501500482d030051102804407a21070881e410020b5090300203200540d10780c0165001c0070303d43c41c4960721002c601441920f404c440f050030004211039260900c2c4810003c443c00e130001080c19a19644020203140c402d0701c03040c10f00545c41c54041074540d14020075500480c00d01c03005100354040441035a0340302c40c8a1415448070064280001c0d0090304209020b0701491905003405103250340041428895136001e200c900102122006022151004580e800005540c40c0c40c00c0c800e030340d10b0040d034ac10310002c01420b142c2410b0301c4c40c0d0918188427542e041100c0403c00261042010b81e08107000c19240300c411607007008285000e120a02d003060402e00c1c000e104007206440c01b03202700300342c0030640158200030b000c0c1c2c402103006019045459005484650205230b074929051800d002038040c400c203541069840200f0741e0715541c1c500b0140c22510a00380d0541c0a400503004d0680c8070385401d00001c0d40180408264140802100521 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 762302715 1250 762301465 762301469
    0x111203041a070f02120703171b1615020708060a15140f0d081209010515061908190f0225020a031506050a0806060301050f090601050d061b0c030306 65
    0x41007400500702140c803c00c00001ca4980542e02e07400c520144d510803d0400d18a034000405d003140342402c00d08140061009010101040c03d0300840d000c5030354090503aa0030f01b80c03e100c254006124404e00c01ca0f5a2034400155120341c0307004644025484030001030404900303c840e5006a55213507900443c7e14051842c000080050383c4240c90401ca400000c01d0751411484440c90003005040c05103030801c80300e441225076590202c06000300608000804a0184c00d05a80e00b54100c85030500a0942d403030464200c4501d00b8080300c00c2c0c86c2c0f140c11006d013a0351984000302085a80e4081840e4400108401c1c007514516508600c3c00580e24012a40b121001c40000c5034a815583c10144001c8016180c90214a003035076081030046400c09030b0740468401a1440340c0041303030450f0710f03000c0010b400c04000401d10302400084000340308959460a55180601007241d100704242c0c00f190042050b41001813109044900488000c1000c9400328481050642e00d807526200044964030180141607040c030035900 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 762303965 1250 762302715 762302759
    0x4050601081e22120201050a0b06190c050714010206131509050c03151008030304021503061f08041713170a0f1a06090f1311120304 58
    0x21a802e0141844642620031600c00250000c000d001c01e4001e2111030743c0c41640c030112682c0d8038000e901480c03c107a04c20001d480f0b0710050741c01c09020400c9040f45020b94882e50b00d0240846007405001c0000782e801c0d40c8012101014040d4060302c542c00319805000007405850b00d060400310300b45541000a103442002403030923696003400782002c800101132003003c04d50020301e00c00214003104242020742c00d1000030080158180f148101000160b0345110307030b40340724182e0b0031595200d859690301c070715469100844000358400020b41004103d01001c1c00915000390015003441c141d8481c640307002800091503c182c2000c6803148080004100c4082c58109242101a00640c142900700f900142c42510302e0041000200711920202e0640204100540310720790803d112210304107203030400b140300d1041100200034104548002070001c0c2440c1e030401d4040c2103504d9502c811aa20194401f000010600c0101c4006031264804c41142d641c4050076040c045141c1c0207181d0340c6145c00a01411402d00d00e40003a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 762305215 1250 762303965 762303977
    0x17070503180f0a0311011205100501020709090309060f0c0615170a0231020d0606141c0207060b03011b020708070b07060c12050901090b06030303042003030405091504050601 76
    0x2075000e0f254921200f044a500035042c252045403500103079820824407038066246403038141003100007208911a80c7c02c5035400e0b000d940c01240c41e159410266864144050045000800300700f004c0c6d4405c0c8148820004540750400c1c1da841d00307960788000c2d6030f2100c5000d10a421610001d02040707a95001e801c85004020004102c10165640800c928000340d5805800502c503030141408041a0030000a8804202c42000c56030340f128041340d84000e180c03600a07034002400018001d982c1003c00c900b1507030040303c68021040c0c982c21040c1c00401039400030303800f2211039440d030041c00c1d0152000d0180100c1c100b0000110791003404039010092034074806501148076a070001038200441840c030300803502d80da078210340040b8060321901d0381079842c03011400c283d125152170003040002e18401988007040052040c0c07041030154440c0310030503507203000030398014108a802c100b0000040d002c40d0f41e03124100310080c0546e03083c640c0d01d50026003855422034140100d190046030290a501c4c00e48203141c1d0008007400c180b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 762306465 1250 762305215 762305239
    0x703150603060524040b13050a05180d05030604020d0207080c0c1c170d1d160e0c091207090f050f06010503090303070f020a080c0d080c16020108041707050318 70
    0x6003200c0c0c0c04401080c0121b41e80c01a14046898016424409500c9a601441941000414000288011252040c544640d0440d1000407940401c502001800c01d40e00c0780c2c21501c980c0d00b0072009501510b8a059440d07420440080029101e601600100074500094a4091086802e1019115200c020400c908008070744050014060b1008003014400350718103a0381350200508410020a444c07582c03214100c00c1c0742c401404401c8001040328810b2510108190b0441d80d0740022140c0d144151600071045038144081401c0381000c0d4121039401048100305c442c0c066843c0200d80c102c0b2500320840400342d80790010442604001c0300ca144d040a000e180c090300d540f428907007194582c00302401c12800c000417030300c81400461007000301c80035054001074281c1c2e40b0760112501e50b41e145410103040020842d07040010b8260003180b016030f042100c44120b004c01014043e401104e010344010411140d200030104154010030100018080091191004658480309140f15149034100c00902600c11441a200 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 762307715 1250 762306465 762306511
    0x1406090d030b0d110402040306050103050f160509070c020a0f150207120b01030212070902030c0306010806030d20010f0c0e09010f050d062f031f0506070b070207031506030605 77
    0x103043d0082c2c00006001c50305811000081c0039200320744c0701901d200c0c10800044103210010a600c08400e1400080350780c2c070000007440004901c500d05ca280c0c0e10580707142c002500c0600503144407180c0d80c4020601200340d13885205000803011542c000b0302500c1040407010045640405c0400d0117031607161200d020700741460303a4400340d29005001c001d01904d4550b11400b52000c0410242d005052017010070754480c07406c0a0740f18030541041300d8a5002940302c10120705281804070704110200170584d250082c071003440c1d416141c0410040c181305015940d9420040c802066482205425034603551244090210481005074501e8181c100e212108002081006143c2c2d90300c604200056002d540490300b40900107541d2101100882c150521024103a1804484038980004500c1410b10740340c100c60490310b0a41061078081a40500e68010900704482c002244101000b41e51201940c4115103086440ea0388510180401c000d0800e0403e0b29003005008000f81405541d5000982402c0d8580010368505 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 762308965 1250 762307715 762307729
    0x5011a0f09010e01020712030c110603060f090601051b0c01020d1d01121103150913020105070b04050703020d050307030905090403210b15040e0106020604031d0d1406090d030b 77
    0x103a0750621210b640310207240c0e402404010010080034440d01d80900050401808100f60018211075006d01004040d0380c0e0310300034050340e0144101600303405203060900c0500100c403d020741010305100c4113102100e9000d18044460404c0300c5820082d0050b150244006440d00c2001d601d020140900308030201561035034610001c05024091074240740c2086100e82200041060a0008400e404000200a0200c0341880c1481c80d03010195031205a5a036010061540da03620210008c2c00200d080081101007607502d00402e0f0014020340640d00d2041d640d600051180c240c0004c00c86180c0c101203121820706400a513104014402501c60b076107c1d1520356801400a8154000030b0114000ca05506607101043d83c404407d580f009454180400725054541032550010311070002c11311f80000000c16490f1000c2102400746601d41c0b03400b0703007800c0e50121058203004241120354100d800c9984010106081000d5404c600c2c0d4950003518660905031211414200001c0003031041c9820907501c180d070354844034 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 762310215 1250 762308965 762308977
    0xa180e0106060807080402060403170309070501111e07091d28060203090c0418050105060406060503060616050114071e05030109020a05040f0608241305070215090105011a0f 76
    0x498140340c41d0b46d4501c0000d080e4043c58001400442040c100b41e8083c000702d01c02103000310292001c07508001d60350b000440311b00c118500c505100360815510b0b031508582d100904202084e0950644908035199641002155071542442040f906e41041c2904040e100380842315542c04034002000070713880308500240785055001e80040201d42e00100050156106000c1d0034590040140140b12901003070700d880d8000300701944242c41c25468000860704900e0139114940841c0d8540d102c46082d5030f100c104211054110040e400e503907000050700480059000c3c0706040a400c02c00029090710f04103548010110190880300d145040c6241d070340f4221075600501901c1c1100e82c04100944c3d221040c0e18104e6150049502c14885803a4040d40810500c0d00010003c0c440c1306450690405a90103203c8141c040710425a040d8010f20724900c1503420907400e802c480d500190500444040c1c0300710f403030b00007104442202c4040e516550740b401031104802c4010303006018034110b590301f41412501e0070040080c4c0f08035 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 762311465 1250 762310215 762310217
    0x1b0503030a1202190f090902030f0a020f070b1003110303033309010f06081b0a0f1b1101080106030b0a0504200a0302181804030e0402090a180e0106060807 68
    0x6998200840d862501100d00d0100c04000d003100e8241610700c01740002003000710365008078102d902c001c01e2040d40c80c400d4a00c11807040c420004a502c9244222000354001911120300060030400c0c0d801040d0480f80301ca001e541c24850768925a4514200328000031072040f11540701e50820000d0002030046100380c580b45e84a6542c05405182801c4c411750810540d00e0301c595008000d19000003488444c0d0000d000455a81351070782c41d500d556640000b0500e80000f41c4440500805104080c440780c450718590404103c40d0900d486150056040322100203101d440840d521414402024000d50b84041d10300e0041207d800c00780001c0303a846000401c4c14401e03001707840c000c66507104160850404075a0313a009126407068410b649008089006002e50f10103c0040303110860500d500b18541084122048034118110009465440307a0f07404503840c03032194106a51140d001e00401001d540d8000103500100403003150f66200c07428a1f00410195074050400200c1a49059020442d00381c00607061075022840b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 762312715 1250 762311465 762311477
    0xc1a091506131509110c010e0c0306070807020c21070609050a0b0f04030812090f030307090b0d0b0a1206061202090f181b120f030d0213030501181b0503030a 69
    0x2911000d0800c1d2035180d40100304d4141000c910349a0000041c0c003d003118018400284004060302d03984560300c00c110020241c240d4442c10025070440c2c89918880e821016501c1500c4500c0184400128500b0f948011140c02088184004041c0304c410880d4000501a41c142902d8035031070000024658100c51240020001d07000541e800d40c0e640c454100c2d8040d5510004068a03450354410050103440c00b120b0007125407140d8101d599840170000281d81c4103403900e03070700c0c24a03250901569250b984c010784a080043ca841d041540e09581e0351407415030281999012000f5152032a081c40c6065840561101146070b0707200c00b803c805030f11000350203a8094011740ea817188685401104802c2d5414411000310300303000d400144041c6841c1f561f5030f600b409404940b00d074070072918014825201c0f00c44000c011402e42c0704108030000c034209038010b05a12401c407000a9001c5540703803541c60a646500c0d01101804e4024003100c820041c50035690030801240c60401002c880c10140070a03030b00c1c810301c80c5d000d051100e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 762313965 1250 762312715 762312731
    0x2117010330021c0e0a031112010204051f020a0c03050d020d030608030f091306080a032a060e0304030c090609060f06140d0e01020a0206070f030c1704030c1a09150613 73
    0x4010400b4282ea0b040252100b007010b552820240e240000c8191128414482460380c194441c8c0c0500030388044d00e0000b040003604441c030a00e440c100e030b840d6031940701c1913001d400382207404201c0104100008500403405815250300c10100241404166903210003450302e481030503c40d200001081c0e03100314281d4510302d0307036845e56a000502e04d80c4815400b42000c038100f14001c83e02400109022203014400d458900e141d10250984503802c8140a803105104801c00c8510000710703200e50000c0f07404141c40d43c203491609840303468504145486402c8203680701e464250411500700715210300d030001c1624002c5640b10906004000b4400c0c5002c1c44104051000460461355480040d4480302411014000031551144038500c042e40700c01c001c49070940450100640f00c0c0c0014042c0c09101a0b1003101d0f6511514260032030103242040c04d01910a501708050620044002a001e5202040800c0981d40d144110301c0c0c070120507403500b2101c48d0259240b840c2c220a000d00390f2505405482c054a2480340481c400c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 762315215 1250 762313965 762313967
    0x40b221e06060f0611060c040e060409080405040c05040515070c1406190c020a052407080c0f15010603021e1e030114011106042117010330021c 63
    0x4802ca8000140b00c5007038540c0081e00a8100e000301403103403603d030b0545880703030349841c3c2115541c0594480e85aa03041140001400d41c6170952215154074030403207000d0b0030b150710b40c000706007118520900c84010503000242402a450a20304c582241c0d424482141e1401c1c0c90365440191403862881941800c0030700f0182e0b900b01d030340c4000c1a2140c8500c414103440304c5020100c4018014841440f09078020882c1e820085942d0070401d500c0300b4103a1660401c2091016100381180d402c0d845041c0580e0561420300011034103d40c14400c4000c044407400041000072a07949403510f40850680c07041d1301f4544100074003100c1004104090a941c5001c0540f01d0706c580c0000c501d500c5402400702c8190135003a0000002c03801c4810801401480d5000303070782d649515030350a0078071541c4440c251009420b19002440303502c80b00c2110701d0014510041c42c60301007240c0d400c211001e0401c840a0700100d40100c02403034040c1d400c912031032140e52217008001600225490b40c500184d240d1040010289030690f1840c3c2411500d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 762316465 1250 762315215 762315221
    0x10050a090302060319150302011e0c02090f1b0c06181c02060703060801150e040f06110a1e09150c050615120a1e1a040b221e06 56
    0x1140c0141c21160b480c45c210340c01659480340180c807420b405c1d242060159030171800f03010700c80035254182c440b1021000030085040c5a0410904d244c01000034881c50040141c0325181c0c0345025800104c161420341c201102400d00300e007000b0030050318280303060180c0c10024000007a042d4001559240740c45a070b120310581c070b034181207860075a100c58990250000802d60340c0050068070820507940c00700012510f81440c0c90070307210440e40c0c950f5407030b20342c1d11700707101c00307101141c101c3c6d0003a100c0c0c20046141d024558a000c16114841c5c0101c3c085603012034a5091103411846a400b00d0841c020100e0019005400180640c1c4060241c8011b000820b50801200b501403050540d000781c111088a14a14100358004880d03510b00f0300f0b0781d010b299140041081800005900001e03103a00000b19139001c0e410300ca500c0700041c1281015901546501c2c900d141556002c0003550189000c1c4148241c03030320f005150941c0e2103041146c202450b00b2504079000105030a950341c60f802c0b07900390b10f080e080540c15003854006 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 762317715 1250 762316465 762316469
    0x1050903010c0f0305060604061d061905070506010f12060b040e070801091101050307090605161a040b0c090a060302032d190209060d0c024810050a09 66
    0x6610b000d0300544410f4004039800183d4034141c0d000c0c041641d50400f881a0b41c000c078454440400c00e81610702c0040700c001051120155400761442c0c0c14801801125510200b16294110214600080d0b840910005001e11409810080d2082c680c0c0c9203081c0b04603015139199500580580d59483c1d41a21a84e80c582007160803074590011540840d80702e0b1a110b0003060700f0002102c5070302040c6030048540d400340c016244115101c2e00d0707222049142c401c0c240e541d5800b128a12241409481c2240d0028050002020003c0008540c1e1207080c64540740c680d00018000d00400082e1100380300c003010554860002c0310a0758040d14001d0388079114450346034103a169182e00350310795089425000600da92241801403040914440e02100584107580d03a004910a4410300c540103241041491000b2140c0d8111a00f102241e20490303c02141800c03013800c4940012201c50ba0420421000c0480c0002e0301c54044c0080e07111080444d0b14000d1078000038071030362902d003000b02800b6010660100d80c501444003800 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 762318965 1250 762317715 762317719
    0x60f180317040501091508221b06260105130605061602090c070218060d1b060917060f130c09050406060608040302070509090c032b0206100b0306010509 67
    0x15005020740204409400502540340020401040011141000c1c2c501d0703444000b06887d40a0a9240d200b600007000c45040784030511001807421460000354241c0c140c8007580220824106040e05210707004040788414004c0381290240c18940c0d5060035a030980103811a80116900600c0344078001006000e008550310040e444100405c0352200c0305d0b0010308403ca924802c03118100250740d58441a2400c1c020342030040d4101a204110644801e124074205402c4140140214065241d03950380120129608080280c5a40b500c5410801603070040c0b407900103880811100d694401c4140d03151a56004010610641000d2403404582d9880ca0454014110b9070007805ea98122a00c0742d0324000900f4003074074125070303651034000c001030b140f849603500c81d010329415406001180d207020200100114040c03c454001c0c020414818140c0d0f60800011036020b454a5071452550b41000541d00001034100a43e0155005041000850700e04081260305079400703a803030300c2d880c0e40f034890040300c0500449000c15 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 762320215 1250 762318965 762318983
    0x2b02070308040f06022a01030f0f02070c03050c061804051b07030206060a09020301080a11040e24070906090b0d180f050106060306050f010c060b0d0c030318060f1803 73
    0x110380f424a010a14064400c140c00b29203004c240c82c8224420410000b800660900d40e842001031a0b40c030a0704160301c15040c2c4a408940d00242c04000c04c100d91080404941d440e1a400c01013003040303401d0020360080801114458141160741840e600302e5a0303400000c80c4070716500c10011381901d018504d02144040e1100c8100c1c2c8030034861034042e60302c00e01600c84030710036103505600080b0406c10f0f0007228182e85c3c4e080b000c0c210210300740c0c0c0c4102d00320302040381180d07100c0d481b0007c4a05003d004c0103d1182c0703101c0c020411101851040500035400000380244080103134900043c000f0355001602001103c5500910070b83d5211000442c4000b84043d0b0601c201c8603030850044c8040c841a80e09401d48640a08020044159264401e0301265401d02c1440d40003031400c0300c881c150f5809200d019101d28061140401c4003109580021010000b000013114040d01e01a010b00a1540c843e03d80980501d0128504181c10f00700039020b800d0050001e0aa820004800a010100b410f806080c10003158020200 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 762321465 1250 762320215 762320219
    0x60c1e0c010c120510030f021012020c10110901090308210c0414100f0c15110a0801080105070509041d0d031d061b16080a0903142b0207030804 63
    0x500d128040f182510f400d03403c01d000705003d84642d01d445401c40350700c5010210f256039070b9824092140c001060250500c002084101d00340d0181d400213004540d0344002070104208420300740301c200c501404031034803149801d0210000598022140f402074030340000354180c444422051622211038015282000300c4002018030240700c41c07420107403043d074001900201c4d0081646051051040007079a1541c0001e8504908402c1c2d1801854640140360190405503010901140444182d988400b072403614002d00041c44903455a10044227409802d01030020b01032810020402002d602030000710b05d02c03c0d662140114829201d60211445040b214010b036528103004c00405001043c0303050341d0400d83c0001c0c0b16480507096000c10101c1c842e24460400010004840000042c9070300164203c0e58002140c2c81d42901140c1c4c3c160240c814000603507501800c4030f0540ca0400c8444810000c1c0714442d0380701c00c40015600c0354000b0801d646190888415131041d0301000220318090b400d40c40500302c04400100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 762322715 1250 762321465 762321467
    0x60315050616080c0f0c13050f06010f020c090f04020103150803030402060901050403061b0f030b030303040f06060b0d05011401030501080316030207050d141e10110418050711060c1e0c010c 83
    0x20710422542160340040c4050300d540c11405a940c01c45010045502401c0021480e40c00360cd2080141c035810301c1102c0141000b6400328850181c02c0e1410050120504d0800045691500034526607070465800e101506203400f110650300e01001c0c10082c4504008030360042183d10031270a4400454020b0018480900380e8041030300101c0f8038091050009000c2c40003546014000d019010810b03401400a510755540c503103500105c0b075101385040b96059121600010804400e401130450303800e03040400645549811401e00c01100100d50b00ca040c1404c0000400415078003105031400080c103600000303404210b9180c100e003455401e402803036011680d202d414080c420a1401200036099410071600384500f03c022260250b0012004844140e0040218590108407904070607911711804501d103003040d8403041d40a4941000c0703c00302d113034070366900100b0607541d60051510860203040c1015221509000151010510501d00440c3c44a0355001c92050a060820100c1d03220f202010000c02c00000e84c890 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 762323965 1250 762322715 762322723
    0xc0206132301031b20060f19060e131703090102180a0b0301060f0302090306010303030209031506011b0c0306020d1d0706120b220204060315050616080c0f 68
    0x204030501c0071404403141165000340718210502e80c1010040541900c5100300b1944c0b500e16002e030b0a40310480002a4929401c00c0010034041e10100c8005c4150b0329146941c00350741040c04112428a5041250070010304100f0f400564018071001c00100c50352040e420082410314141300206510000003041011500041d40540a187e0000c0c3c60005408220320400800380c05a01a40c1000d03081040104201401548142030010403800c0260501c0b03001c81c00242042800d03441980070031703000903040a4a02d01440010406480060107440504103100000c003d1030040c0c104140161102300e01506001104a16100440c0c2c062025076542e0102d040c21405440045d90208029904c03c9c0001c01260000c6071170803c2e6900740d550390814480c41c0700020302414003101601c0c1c020a050345c0c07405620f520598209216465501702590301d03450402c0080c21201203441d03000f000c409071a014862b544c2ca00c400c4810a500d1403444c40d00301c0d43d143c00c01c1d80300c9105103991000e46125203c180c2154a078081 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 762325215 1250 762323965 762323999
    0x91201060501030e0f060f0603070e1f060f0e060904020d05040c0f12030806040506150d050708010504021c050a060f090903030507050c06040f03110d0e150702010f0c020613 76
    0xaa014003d01d01040c001c4c5030b5802c1d0184584d2440d40121000440558a8034062984600c0c018101c885690752005640c1d07107680181c2d2060040540c51070548400d5112034800f600512407494010b0b80c40089900080545164144082c4600790020b450f500c41c8c1d8031a011384d10300540b03d420030402e81c1400e18010300100c5262140044040c0b644038009001c2c01d48840190200da015114400150380703800802000b07000041130030340d1000e2943d00360380d03001140d0300c060074802d003000c0c5000032641010140a0100e0300143d005a201e980100540031040680da403924060200c400f101080941303c01e0801c0010f414070f40c0218001030801c00d800030310000250010200b03140251410031680c3c403240001c592600c1208120201e9600150205002414030024182603a00a1900c074403999407198503641060003003200000044c03840c2c07603844070303a04c0d012200c0d200244805810603d400015070000e010b40c450707090880700f030003101035000055488070f070116030610204a000c20031050700d03280c5503541e6200c81 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 762326465 1250 762325215 762325217
    0xa110f090f040b0307180204090501060507020901080f0a0f1e0c182007170a09091d150c0405060d06090506090606030c09010c0c08013c020708091201060501 69
    0xe500076040c2040e10a0b140799032000350103009658280950648001c1b4407214202da0107600308800100032140d4454580601007665a0319610201401048024030040e08400e01b02d40110b000d85161210000303031015070582c8005d24002c1001c05040105051002c074000001c0320039100e140d002084680240c05081d5032045d1891501005034104030f100b1103500000c15003501030540414040d0031100e0780500a541d201e01c50714500c0038003407030003503600d90030450b044004101c648005204d000464042e0084c200440680c50307608089180c00d503aa0f4000200d1180918286030b0301090341740d0741e42c0781107034003801c1c001e458141c2e170781c2c0c8000020780101018440c040d029494100800e1041c41c1c400704060140034002e114600355180c81005101c0c0e6800352504506000b035500500f0005800d00007210f000703250210000030003500c02c0b88509002c6204e6081d4080141c0012200280b040c0c00d00d007064060390214000588410341071521000358402c00080c0d55001900000100f18500150001010f442007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 762327715 1250 762326465 762326479
    0x3040510050405060304020f0f041113090b1810120305120105010f090b0c0703060f0603021026040f02040504050d090f0302060414180703050403030b090105180a110f09 74
    0xa000c045031a400749002c1c0e1540040104045800340c80c085402100700c2d42c00501c10400e600818000504844045003c5481040301064100744040070705501802090581c1d4203100c2d0300712000004c0c10700d2507801001d901c2020781c4e10102d000b443d0b4038101c00c0c1c0500440c4810140f840c1302802c014185800032140c0c000c601c0315900004c50030354410500388880f14001c1e114440c1050034084100400e40240007885810f2091802c00400702e5214010700b80004207203200015042c1c19801440025429034610340240070070240b5240c11058143c55204030f104119100c015145c42d18035000120f10040d80c0d001e54800d0a01d014401441004030706d1060019031a02c03400303100d683d501e41c40c1034408141c3c03002030341c0242c00340010400c000c41c2070800c1148840081034040401402d5181c240140e10555a110009680300108001c040d018801c1e4039003280200c1e81c4862942c0342400044884070601400143c090300791011900012150b00100780031007402452a8442c40e00001c29411900300000311031284030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 762328965 1250 762327715 762327739
    0xa080304150b0f0105071412070309080705010201110f0d09061d0f0d0903080c0c0433030b0a0218030601061107091103061e0a1404050a1116020607050d02030405 71
    0x9010141074003002410b841d11742c28240c1c1900c80c0d6144500f0001f40300954040d8804240829003018018042e881c0300362070704c0e408070382441d00007450b00307401d504101e06581c5040545c45004800c2c006403941e1080504070b096a4942ea80070740300152102c0000202080d081901c42144180c00c0d51440764803540101c100c03074904400d803000d42c0d501e1300e80e10b11001c08a20385003410f0001c915424000c0c0311400c01001118041140d41b00410b04071107040c030400c0000401c402c404c180842c10030400180d055851480f0b0611141907465039a48101c004c0d06451303441d0742c0014a07900c0c08100003000e548088004050310040d41c1d40350b40140114140302d02c40e039139601a101010800074203038030984440003100644076040d07541d020b050110801c01d04910364031000c00072031240440e540e00e00051018007e12051031001c00200380c103200030740b00042d088003942820000c043e04a0a65841594128000003503440940740c401c0c00803d01d58480c503100a44036000d685030500c034054001004100316401525020450340d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 762330215 1250 762328965 762328969
    0xe100206071407020d12050c10020408120c0a06060f051008160f110708010b10020f0a061d0f06221e030521061207120b090a080304150b 60
    0x40303040790054003107401d021a10402c0c050280203070859910141148101415989510a119011141c5d0000042d40001d0070140d0786010b00c80c0308520440d000c0213505242c1044c003102c1d283d034003e03281107403828400300740c4d0000000d0800c0303022101a0403607400c001e0300380c841d903d00109006900a05010742c00110702000028805c2081c070744130311040400026035034030074082144e0792402c891241040128041045036600340c140300502c02014a0000019851600c1d4207014813103070f100c0154419500080c1d00200d17240b501040c40b0707600e2623010800052801c4441e641c80010184056007000b184900109c455005000003041401400d0720b0300c60020441003c448071801900024004040b0101050b40f0400326120504410030343e80f1904010381010089410289070319041c13851070704600c0e0510148040c9042c84080c400c80c25020340040c0c00c00034101002c5074250070740080c00a00c170b0350780c0e80300141c003030300d41401580855644200400e9032810242031401c400c80407260000b1030b1514001c2e40c441c00d4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 762331465 1250 762330215 762330223
    0x6020a11090405070e07020606030105132406090608010b1302040b0a030f09060f0c08180d0804060f02040f030c1e06051303020a1503060e25030f0c0e1002 68
    0x140d0303100e05280c4542010009220040401900840d003501c50b206020030500700f441010f6200e03a500b40c3c005e00d40391416204050a441d000f401c54801c0e00c0c0032048440120b404420802c445481264189500064a0403a0fa006080c43c0d8480401d00d8030788a40400c2041042d04030010800c07040381e42d20380001c0d1040c20380d8201e00c182d2140e680300d4030301000503c940c64080e0f00001c91500107481c0015652085440700e5003550345506c00808071590b6403140c400c40f1138000b40181d8020303103003a021100c031314038400c48159540304e03d000250034400b00e94002401c11040341c215011854203400123545032070341d910150100a04900003113a01c800c070480d0108900c000c0803202007072502520f200210711841c000090394264042108c0441120008502002684410329080010044035252402142c0043d2000f4101c81c215040380c0c0301c003155007092051102e010100203850082c603040e410000c03607841200358001c1c0042c0e00000c815900f401c2d0758044a940054281c00019401c0d1514195a001d5120480c0c403 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 762332715 1250 762331465 762331483
    0x803030c070b040501020f0d020415022811210d030902030a06020711220b03010506150903102f0c1f0e0a050a0507080a030c060c090b0706090308010602 67
    0x240d80000d220150200701c8100b035180c1c11500441c001440c000b2100365456090380b110300e49400c1c0b03d800050400c80c14061500081d004078003440501251103000481e448801041072016500c816104005d009000400700e40204008006002c81c1100b0607960f0710140310406070420070f0322409020903840566001e80a800c103000d034010060207103a8141d0b40c03010000c5d04001d50640e101e42180c100c1c16000e455940c01c400041a03915101d00d5041c0c246044041680c64000406001e641800184030013a15144500030710b115001110380d4a6202c4280480d2034600181c41540c1070324102010105404400744a10390a0159841140003916211703080041510407030400d404180d01c4444c20070f614003070003002c03040c201c0c0d001c41000c130b01c69000c003c102e403500303c0403a42611301c1c0c1c000020031410400100141d40042c510000980920801a140540f0300f000240c80580481d131100c01c00c8254078400ca45d070b0310181802c100d0154450045041c044010591160101c020421a000104409000081c0c0c691 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 762333965 1250 762332715 762332731
    0x50d080c0708040303080a0603020d0302060405160b0d05420607080d0f0204170303100f08150411040501080a02040c0503090c2e0503161d09060a030506070f0306080303 74
    0x460686185d81c02c440c2128000c000480c060b60714440400146d88500c5c00e400c0701e0740a6401400282000d007010b505003540b2001501c0c0303066100e401041210007030410360300309101400300000d55a030b52825070301c60316140c850111180706880d07400c00d0700008003c0c0241440c00c000340350701995242040c1406050300c11a00b0240100c3c40c280110384560340160008101542030086c05401c003903036944440050310581c0080c288682001c403c10602540481008000b88919922546407034546284a910b521000d5400625881d20340006810700c220210307846410b01010b0800c218640e1744140031070f29154000030403407042d070401c01c958240c44d1040007501d0103100c68102400740c0d2100e00007009140d05400e5031003406ca08c0f9002464881030040782014800c0391850311a1a5645498440600c010741400302d40c00c1445041ea080e100049040b03941940241400d65507036002d81c503060006841d0410a03400107020340300e07510800902c80c1d40045405003c0010351414881c8a858501460302ca00003110216 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 762335215 1250 762333965 762333967
    0x80c0601051c0b1b1b1614150408160510090503070626010e01031203020408070303080a180602190804050316140303070314330102030f07050d080c0708 67
    0x30340400c0c000346040d1307080466188804260b4000e6203480d11150041d80c40f0000c4400c040f205081d46180c144035040c0040d0580b1000b89000e8144404081c0d0080d219007000d0040c0302480c610010f049482003210041d1a20b90121599000d812204100e680c00034040e01d401407046640e03042c079046c000c84100382a00e400a01512140d800d003101200c0203048a200c44000c05e203103415040022062501c118040c00c201204420103604604004810302002d1410740201071040208000500c000f01e0040c0c2074036031504e000e55940d00c07003a00d0040580a10b8045a4010313008189000030048140d0080c000001c0c0801030094100d00c405060700c0621080b2806840d03a001044100e1902c00450103000c0001e104480190000c3c1084801c07501e150011603803c0003007650740c82108000b0008100542e0321120103018400c1ca007150442d0b44403218100070045030002000b01c100eaa080e8020300641d00c900316141801c40d155140c0381021582e901c050110300000c89c0c14200403923802030b2680c1c2200d0342030303400039142 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 762336465 1250 762335215 762335269
    0xf0403030e01090602070606060e2d060417100e0f0304090e01060f0f08013e1c0f0e0c010203070308040203070e0f07030501050307141516080c060105 66
    0x140e0150030940410100c81d580c03042200c0000301284090700303540f409940c00054543c20840041d10030b04400307205038401e9040401d07000202812024107002c0100ca0030121812650321400308200780511b0300a00c00610840048520b80e81000601800c02804010184125054035469640741d0a082c7c012000903081040180983d20458200300c00500e90348000082541d80d8511801800c01103410000180c80034031000c101d003035824010055400721f041241c080d030180550351300281c1024900030040d03504040d07000c1002121041e059411801840e0f40c00c0000030441061100100b02d107080c04010f207460309866400507040025034440f4a1410380040d4508402c54400b40e8a140006000720f9051080c0103000c0b482d40706200c2901d00a211010318060142400721005c0c00340c1e10142c10003030086d4041c590400250034800900c080000090340c546451440e100d201f4120391107a07003810000201d804458104020070440102941003c210507126a6600d46082144512803940c03000e1503c0044800 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 762337715 1250 762336465 762336467
    0x30c0d1107050609063f060f0f0301090b090a03020118050c15070f03080702150708070c05010609090809010210090201080c0a05122e0308031f090e06070e04050f0403 73
    0x906444100500170390074481642843c0c03200005141112070f4901445c44098840c0c1011101003040e800700300240d140900e44400440c15103016150300501c905030320501c807203803600c00b94051021a904001410114175002c03901994a1807a21800c41c015880d00c955400d182c600301035012040c55000c0081d003603905c050010080d0b0603494500103070b076030001042180006220034414240300e030301c6600c0740c140134988000041e06000d2a0f080d8441c280c02c1c810100300c51036034803030003003a4094040c3c100702421a117907007401401042c40350021605185010684070a00070004064101000240c2c01c0712803501c114255502a1418108000d000c2420000419891070300d01014201c203960b1840d11505000420030600c1e02010103135949540f01c0500310182c60b13000c0d00001c1c003599000d1703401d90b41804185159681541c40c84000d000c0300550000008180781d44010300c3c0400d00402c0200d0040c0031024404000b142c6032041503803160042400004154400d00b8076019a1b0310407101203007419074541d1070b620 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 762338965 1250 762337715 762337717
    0xc050117010e2716050a08010c1205130611190f0207090218030d091a16140106030c080303150d03021b01021204140a05040513030f050708030405030c0d11070506 71
    0x102d0540100b43e80d0001c0b42c520504028000c01d040c050444900018900360500106d003041d074111644907410314015a131211703080002c1049200000d80f0000d5195030340d0308000c1c110004860018050342c144a5800b000300c109030040d0514105142e003816030a800c00034140e401c10f40180e00c000141e0000345080242d10080d901400f5225006c4070640202d010501c00039081c04000c1019401140c41c07050300307004183c1c15081e615121481b003c551890074020344051300d40403070705000040002141d4404511345003803c1d08441e0046500c08800070806840b012003d4481e00b04450b07404000d008880f440d030080c0303840d0b280001d8054040d00a08240c1c3e1400f07400c125540b00d2084103606512a1503506a0701808000050000300031390b0050105040450f42000325a038a15401a8400d0782458144540c04040485442e0495030509013210310080520050340c045c041e4540203059110f010040009024000c030003061000c1000301070340d1030781300f41d04400d507815018845450151307070140200740030360f00f4588 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 762340215 1250 762338965 762339001
    0x204051807060e01050f0c032a07090902041b020607030b03120301031b050306070c03090e1b0d090b130201030e0d02060a2a03090308070507020d08030619030c050117010e 75
    0x172501c18a03258000340d441c0600e0b0700191000750319a20000304c0c2d542e1048000050503000e106460314400f04954540160741c0c0e071300c1c103000c0c031250b003540c1b006007038219912a4040e40700da10445080b0030401d41441e001030b4988000721812800700b802c081240c1d1030b80c94089644900da13051040124110703421601e803001500c001e0041c1640082680c440442d07584e40410896108170b80695541d1200360399464000c0401d40c0c243e106a500d0580d46084c400055140381c6004951920f004445840e02004022300d000340c8040c03440541040c10001c00d02c0384081084203100201c81c004e0300c05100d5103407001c1d401036540001c1d04203140140c004401080b5107003240c0d0041d09602003c0c4a0209003203c1040090901108c42e81164003ca60380740c801c03000f0140c120301c01d01e90024513070904c0fa041c4865500418250180010b0041c0601400400030f0036a56909024041c11003202d005208d803552280b0342403c99401e80c0c0183c5001c100f48500228042034080c9040307050f038580c040300f5981612030f00c882c4070313104031a1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 762341465 1250 762340215 762340217
    0xa0305071a0f240603070507170a05040510021b010e04060e09010e1e03160206070f1b090c0e12070b0c0309090112111012090606030204051807060e01 66
    0x80070800701550450005a00681000780c801466080c01e903030780d81c002900b90964202d099403942c0110200c0da54401660b500c00c1c1c490424980c3c0d101d10345005441c144002c0c441c032442007808154112a035500002800c15a5001d4950891a1191050aa035101d83d0b000740381d800041451842191540b1603000d410140074003500c0403d5250b10780c281000403000865010b80b586c0e544080e17801035040204102d003a80f00c881d240c0d854030302c1d5000d0300d17407526481081294501c52075001c490300115142c0c031088409650f040001c2802c405460700d010104000c00c0300714040150708290012030f0759802c0c0d11800001d0032154448146080341d280074000a92000748040740140181c03840001d2034a0220000e180301c04401c0d019590340d00c903020401220400680203440002c18102c00c1c2c40c0007400da0030b001b8812000440780d43d40031034655001100d03120130b80c1c10601450380c00e00b9014410041c2030340104054034070840b028400ca54031040400d2218840306120f1059074082d840c01c025090059410014240e01 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 762342715 1250 762341465 762341483
    0x10e061315112b060803030a06060c15022a010207020a0f2d05060a02030d0507081608130210260903040e090307080307090e130c06110f06040606061209050a030507 72
    0x10f02200300040b5201c42c0d115107441d800000820044016602c10803002d810750f82082c03035110105031207802c003a1840c0300380d48824940c0020401d40e00c110300c0b0747d070000303020409550581200042c840700d4041c2d0040c2d10101d000b2081c64201240a5003004402025901c4424510041110f001440c01600c01031580854001c81e0001d804265a16158000d00650f85640c00031a07682e10f100c071451003191401400f000807c08054140865100b9003c0b1411007400c0503c0c04030126214641e2001c1c2100e02800001d50156420041070400c64102c0c04404030071504408003d41d8040c96555040384020407101913074150010407081c8592001c032080350303810103c00f108807070501c001c41c1c2da040ac46610507110403020516a61040006041099031690301c41c480704180c6500340d400b940c560740004a14000e02c0f0a0240a861f864a13101e000c1003559599080c0740211040c1d8185414068020100c0e8090b41c80018262058039a004003075001d000341c1c00e41d0241c018086140c00ea10308a4858000c01c4040380e100017 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 762343965 1250 762342715 762342787
    0x1050f0103090c0f03080712030b030604232b0e101809050901050a05060d02030606010e132a090b030c09040902090901050610030e060103080903010e06131511 70
    0xc3d032039136450040d520650903a0b554030054207004240c5890529820201070600c04100d01c0f903240451100d4004d503001c01c0409080311030902d81252401112050140ca1117022002181d9142403014440b66100d89842c401400b0724411080300c00c0d01040038141d8002058100020855124405142c0401d04501e14000000e882e901c00c801030ba1010303100c0c04c515a4640c070030322101d56118841c483e08000210b4825001303134580e0740400d8888400030034543c10f10a0005d001d82003921601481a41140100b00030001c00039900d0740c10b0f04000c01241d05103141420008a00102c90103803c600b0161203c94103c141103039511014241294480e80707901d0340040e00d4081900058071024013040c040c032510f40002c2a503141c400d051011400e150380d5400101420a000302000f003001182690640360031000746641c0d41d00301400319004d4811700808900d00c1c0704003010020310144183d018607656100c0e00c811540d921803550704c80c0c16500c89050192000404100841075102c28602506001040741156400a1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 762345215 1250 762343965 762343979
    0x50712031e061e060815011e021c050301030b0103141212061905060f031506070311060a0911040b010915090303140712110c0301060f1d01050f0103090c 67
    0x40c4001c000c2003032074944034280b0810080d0300d000031401c852144148100c0d46407040052a801c4c02a00c10400e8000080221416074410004c401201042408060b10004001002035407a10018406107000c5000c0c00040c4e2200d2246044904807500000041616400e6071904000b044110500052601c01e005c0c14005820140c80540300403566000202c101c0c0c6401400d000f101105101d561a42c055008000c0c80340b0364510082d2010703001d19404480d16642c6a600c0d117482d906400c1d004075808800844c407170040650041d980d000e07843e000300c00e6034103a8940e0071000056900e14031300200042509545075015062aa12080303090805242c0800444d0b80c820521030f00c981031060500028103420340900c00d05400088041d03020b06200d0f40b01e0b250004946071296640e402c00032040400c00340e550020314184081114410720361008000308420b61b5544c5942810340b1662251440d19507441143d5a050130044d55164120b480242c04840098120801100206603100c01103521001100340480c0c40 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 762346465 1250 762345215 762345251
    0x90309010f030b1c030206150a090b0102070504060b2a0d0804150c030c110714060a050706021c0e0303130b10170106051503070221070b0901050711070605071203 71
    0x450b1500400d50b13000701e181c100203041c0344008000781281440406203184685400c5403031400c07280030810000b0760b00310843c0101c1c00c00c88241c1c005944a0704201c008103d00e429080240944400540c207041800741141401111044004980c04035410021402e017005005009582e485441003003010b24480c03200c003803403084ac1e88400d08840002d0761021030704081034110782001e0410011350000c20100e40b40504d8080228084000e47e40030312004500441a03e015906403000030707a02403c1952203540c94010118080e200c0f00f0350f52180c80c1442c0c0d80711700d0840701008507402400380c480005600d50142e190918010030207401c0300c0d204141d400c03000900e02004842052255601c50000c1005490301c030030010000c6510b4854010507108005002120ba00011136400000c858561a03100c50150000c07114940681c050113000424018100315072005e0642c0304500c564201e031a00c464840c00f2048156a0307101c24000c00d400320780d0412041c400300300e290b0803400100480d031a000c10400140c080c96803c0b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 762347715 1250 762346465 762346489
    0x804120b04060c0203040e220212030a090504060506160302101d0f0106181e020a030903170603191509030224070f0f0216140a090203090309010f030b 66
    0x8503080580600042200714090300d002090b00d4402181002d0402d10038a03c0d00d074019040303002d104490f50511031210200c1d1510b030003840e0002d0544d00e82c0c004018203692290305c40010b940c00100302802c04500f40c54184140b4054840140c0348134102444110103a45005c041c400c01d170198403c0300303841d58401d0114040d40034030740d00d0140c405840b11f044401c0c02e45415402540409107906000042c000091149110b003c41769041c0301c04038144032482a84e4540381e0103502c91b030503c240000345007414250941c202c0c002040c800c1c6e948607020001c0075240c1c1c51041042da000e55060300600a002c0d8001d0a4450402031503000c0c00c0001081070f0300c0c1c640201142c640c840100c0140e001a40b0101e80a20100e2040c10020b00442200c07820349410300f00240500d22181c0c00c07205124540d007900b50b2080c420840c0c490010b5000c0120308040703480b0350301642170060448805121b01640720303000c41c54802d54001d4030702507800c0c2d10041d400d0031010001074807481000b83c00384081669404e041d074240d50700d030111048 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 762348965 1250 762347715 762347723
    0x50a0b1c03091505030403140403060204030803010e10052805030f010b19030b0c0f1e0c070603060e01060806030f03030c0909010e15060a030209030624090f0c07080412 74
    0x420400d061030041e150180d01e40c05204002c0318040d40722034a507040400c4a501540c140750850b507414460710241c006020b1500054010380c070119000c810000800002d5050720b203d0043c82001e0f541c0c51650301c151b81c03054000c00d80c01642c50110550075804008010102140d0147d40076805034583c00800e01d000e181c08040360740d903910380c0d84080340303401c00503003c0e2103125201c2824401c00d420b50b20303402610034000e40480c10a002c001004540f000c502d00c290340385403916083c096501d00c281c0c0c9140911390082c0c0040302035030043c2800051054042d00c42d29040701c3d030700e01010710103030720705181518030102c010140c0c1d82502413410250945c4800b07100441c0309401a085060f00e50001c0c409024510805802c0480120700300001c0c4507070064500c84e4000c0e213013400c50f00c00340e0b66075884000b24064022611420b030144160340900c8410602c15101009080c600000190b0040e00d06041104a04040d2000c0e9050f00340030011480800800004045203170089108914007555014271088280204a082d5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 762350215 1250 762348965 762349009
    0x3062405161a010f05090405060c03250c0308010b211803121e04030e040b03011b09030203011a100e0f151201060504060f030203090c090c0a0f1d0103050a0b 69
    0xc8074001200d00d030f91005c2d00040c1e800b13a145181a5590a030754000282422781100008000201a220800216a52900c058200c03500d0340951050107004140814001c03000b0802110010419030b00220a0320f8030110351920300d42d08494422003c482000c405041d0090003015000b9944143c0c00030002400000c403200800042c0b031801030481c1c9100481c20140c01c0703401c1d40304d1082c440426484001000d44034002c65002075003003c41c40000f4014501ca40202008603a0286062210380d04403075044200ea0080d0000c0c41451800503019000041001a15500940c0c3c03980d2032028034801d034854036500101504070b02d2102c0600e07001600300c4600d00c0d441141114001549070719403042e50351303403401400c55003092801c1c03604080002d0310360b8041100c40c800f010740c040005140101c0400c0000004980a03003990100c0c1004241d0a0382603100030031880119803400d41095089204e91680c141202c1d03043c0002c0103099141d00110090000600300d201c00301e80312040032090b07995660308a14071002c0f000c40d0b6 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 762351465 1250 762350215 762350219
    0x605010312020c060403030e0108070905091e160c030f09031a160305061005390f0a0c050108090f0d021b04050f0606071707050106030303062405161a01 67
    0x380f402044040990240d00c06010410000380c2003003504107030040c00d080c05030456403004800c4036502610340c8495401400a4103210280c00c076001411803071010707408498803558545902851a13a0103104c8840091050104040820f03c6441c42c201d08000620b030100d0312983d00d842d4118680c0300022400c43d08030740c0c8400e0140c1440d4a400415100003242018441d43c80d0030303000107000d407100d081d6030303c02c1c00350014004042014441d0380c03400e1002085c410859100e242150b02d00f412428031940030301d610591136000a0940002119490564440d104941c41c5051000450310300324003800048840c4500140307000004018850400449050341c02800c0c03a44007180034050708003400c0d1b04640128501070a00c58000c800060b61940f08106030f81c020b58034049403400b41100d80da4030004800174a00820600104041900a84110390082c2d90920035213446003075081650b11003c080d0070310203040d450208216405207000e81065400182c0515690305503449690201d16040070f00a03041c007520b401 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 762352715 1250 762351465 762351467
    0x1006030b0f071d09090118060c180f03084617040f0c0308040e06131103040f03020c03100e010c02030c1b151602040e0d0504030f0f0605010312 63
    0x7196501c010310b0718080e5807500382200654106007082003014043c03240e00000850060f003d4128203240c2c01c81500c105d10300c40ca907080060080005040860004140c03043d4144100c01450664003540e03c04514281d4040c070715507850740e0940c0030b1114031420b443c505240d5086030300f0501c0130040c16540024400c000440070280310880300000001d60040c1f00c0070391507140e0f400240c4051301d940036601c40401d03043c003540c43c1802042010075610050540b440050080741c882a15039045000340740c20f58040d10b185240e400c4800665146800079000b0a00a0000402080311200c049250f0350080c019107a40d10010000300b03041950326212000060f44030070402004400910a02d0300000ca0703880550700b41011291600c3c1c5500701310188440c2071019030a0b103401691050b140e42603500204410300d944040d480b402814502c5c40808c182d104516040014450302c00202e2020b148607081d42d5207918003412765542e040400350001050350403495040d02400001c91500c40d5070301850141417000c04100301e0b004 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 762353965 1250 762352715 762352741
    0x7030201052203120e0d09080d030c0e01030f09060501150815031c020715091706190c0c0501020a0309171e0d0902041406010306050a0e010302121006030b 68
    0x7120b05495030155401500000d44500c0102c01d9252410740801c280400a0720060409080403052030300422400a2030039800046c00c004440e200e074141d03000480340b0300b4250102c0b01040c02e039101055001000100e107611030f0740001d4541e5404040000c03a071556840750000c0340d009070000c000c0c400074040302c0480560450207282d406010150f8034000c0707132801740110f41c444c07441d2030719040050740c8400300c1c104140c02800f441d4094984c401c11400c88074003500c0020601c05440c801c04980036084600c840c542c140c0442c036544516045005095101261610030009003450f110b410100070030512510001031080c00100481d04003950b02148201c16414030510840ba0701c0d4400413000b40030401d08007602e081e00440e0b5201c003040c00e41161186980070443d0050645401d00950007840c00c4020703040a40da00c150140a00700aa130200009526003090207a2056075001c2c46c900484048010001441c2c03040000c407800eaa101d0640711800030040911080d07510a410488280d0300180402204001c004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 762355215 1250 762353965 762353971
    0x307091b0516050f03030a150b040b130e0907062607050f1e1b0f1b0d08070507170d050415020304051302030f060402180d020a0b0a0306141206190b060705030703020105 74
    0x3c0001407000307140c04104189c81c8103502c10040102ca0110b0241961402c151840009000e000c0d0502c41a20b4a0a416a00c4a20300c1c000d000100f011852600f80ae1405119581013151031207421504544641009a6450300004a8900004402c02414080c1e0b200001c10200e503040d41d15010703407a1050705280c1c2c120045480aa0610750f030200416031450b01c070002da101e00c103040c610f5510054444000202d101c0b203230300083c0038040074400658441005400201c4104642c80b82e00f200000602c7c84034641d881d110510109d4000030f200340024041030313034030288840346858030780100e9140c990f031036010440500d01d50700380340c02c0582c1c080100011403840d41c4107581c0c8510112402c600d40b507a0300da64002400584a0302da80503070000c0580f01304540340d134904074000d4a6140c4009848252550004015100c140500c03202205024115400740c00c1004141981648150140107641c1d6030b41e4581d01c61040c82d0390071100d007a81744d401008680d1500402415201d0141002c0e5035500d19904001c0e00f5101c0103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 762356465 1250 762355215 762355241
    0x30618050405071406070209070c030e040b1518040c020a0b011a1b010f1514030a020904031812080706152102060f040906050307091b0516050f03030a 66
    0x30204800502c000c540c250a96039040007151100510002092890181c968001d421812a000340402c440d04070840300b04d218170a07607943e101200c4000500007641c0c5902495608619400250103510181402610750010b41400110b0503a2030480018155003e44140b81e0160f000156030600b44080e408003d4003400b02500031040c08594000d002d0102c0c41941201100c44550203100c101c01e070401c2d0400841000b0794142031240740154800445212054031545450b807411072444001401d01081e004d101c3c54000b40109459070b16500c00b035031a444c1007078012141c100c0960700400c07141140c10801c0b0126010f0b0600035226030710b80c80d082041b180d8140c030041c440c00c4001800c04c03000324614000c4100b401c0c01c2903252030701007241c408100b060144c102c045079144008940400c2002040d44940c1c100d4030200d044440d140e80e40c21980003201c00c0203008542184400c1c841c00340440c001c400a02d200c61034140d40040e03030090740d129242003a80c00741c03451640b074100000b4070289031951b010b4601e4540b16 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 762357715 1250 762356465 762356471
    0x503060c090a05010f0c022d040e0a0b0615130905060d05070311040915051501080c0409090c0801050703050703150f05040504030507080f0702090c03070e0d020604090c030618 77
    0x80240002d603510000e1041d107041202800a04050314411400c2440169024042000d04d0301017100b102d15201460410b00007002d04810032070110315013801165801d582000151803401842c1d02c0c1c0001d0350400070318254200f69100600c3c6004c2c4e0301c030310007040303141c030141e00645e049428020035109581025140c1e5100b0440c901038000400c82c04603000e81200c3c0e101030880c00900c42034011501a1902d4640503003981c800108948890049402243c42940b080c25103c40420f90b080054900200545882c00c103c1d80a100034042d03001e00364440f1203c180170341135003808155182e000c1800d68004a480800194580e070034490f01d50340600400e6403d10070b2541510429040c034200958911080c81441c0c030840e100d1010400b03160050b400c44800716040352015030354107903403070764134010b80e00c0080100d009101100004024001000a40c0d004034071559a50100c8103401d400c1150305291414240d9000300201b0000882ea5020300c00e10b0b0003c269600c0104840345004d40c012029000c00081e030080d682 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 762358965 1250 762357715 762357727
    0x40902061209010b061908130209071110021b01050f1315021e07020a0501021f11092112210601120e0a0308090109030203160309050411030a0b040c081923010503060c 73
    0xe0ac5180d010350091591401c00709500881c5a10340c41c1845891000e009a403000846d0440508203046024803405540b00a10503900c1e15044d01e90418001c071852482c5c00d020001e1000050100018646000d04510000d030611803042c0080e0102082d601000401000000b00b0108504007034000c0700042c0000d00150040702903003885071020171142104482e0a40c1c4c1d0341d480b40580c02140b820340340452070242c240c071040a120b4800050001e1502c6480302103200d0039074103546000c1c0f03000845100c11004107050942d012200d0142034940c0024151707605004004481400c218024480c2055980c504c00003803030003440d40e04001c0c05103000035190000301e0341080041004a074000044a003c05100c5800c4c40c5030380c01e0b0781020ae86030003407078116640c051304107502c400403800c07004023440c0500740382203081040146010030007007150621480500030400e1180000c1c00400a622980c281c114607020200d007443c0040c07000070909498250501d40e510740c8100600c0541030400c00158082209005c00346048 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 762360215 1250 762358965 762358969
    0x10030305030c09010c0c0303030603030908061009020c0c0d150b01030504020604060e060d0e102f0f0c12040e06010c030219020a0306050f15040902061209010b0619081302 75
    0x44001420b5815115000a0800035a4801c083c064580c54015040c0d03000c1e680c403454002c0c068000d612040e0001100824082544500460490702500c0340c11200d80302d1a00c2d0400640282d00f00b07038581032080c00742040c0c1c00c8494981040c001c5106100381c00c1c51032200f06e40d0624800315200310543c1410036140c03008110050300c0d203400302e4007916010f00300f200002c50044009440d80c131845560013405400c0000340d1021490004480c044400e00001c03c2c40b0000890071a40e425807a0a00d5095100b0b510005400155480c007000b46051074000c00744525104400c0403452928114840f5007a00c007600003420802c2c0c1d4a480d034016003010091030040c0c03814003d0f84000b542c800046e07181c22201104008001e0840d07031500c00c46401540e1007c411b1002d40380000d800440f0390000c45002960340c18251050025140c948900c1c4000c5600500c00e82c01c003041040c1200c80780d140100101155985c9003440045503460102402040d203d043c0341005420b40f45074010311f580c8000d0003500e403811400341900016 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 762361465 1250 762360215 762360217
    0x15020c0118200d0b090c0d0506160e0904060c11190c0b09090703022503080f0c031b09030114040b0703060b0313081c0e030d1104080601050105160503030c070203010510030305 77
    0x41c40e001400c0c51340c80c1d203400c00c400307040898070038100c1c3d4084041c400311010000d001c03648900c2141095141d41004030f110703a00f5245042860032043d400f165000008000580960120800c201c080c904064000f0340e91884e94503044404203035011242c011000001000403001816003d00703075101486043c000c0325808510340d201d0240c0304009241d000b140c00f030301400ba18040c41266022443c0f181600c0c00c100d09000c1e04c2c51805603207110700d00b03a400c00040c80d540c120038112405042c1030040d0101900031030301c49680d02d0b0040c400c6943d16548850b0186d180d6514403641600447c01761070024440e041080000c0c04440c1e041d0b00c42d500449007131040180e006425a40c040180781c1102500d076454101c600c2085c844044004e0020300c6600d80300514501c000000081c1c0200d28120724108060000b010718442240150f200d1162181c0c4190b0050001c0d510030006482d401151080494507100030365102821900103c41035031520001181c20303002c0d46000d0040c2a0018841750140501c641161401005 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 762362715 1250 762361465 762361489
    0x3180124030f06110d14090d021c021c02060609100509010302040513120207060e0108010e1b070b0c03060f011e052d0d06050a0605040315020c011820 66
    0x560b88118041010b00a0507000f89000e0305407842c0440d43c0f0021440d0080080c00c1c0030546002682900c40010041c00001806190140351500100791f40d100d410300481030101d0103041c400846c011800202481c952411030300703804441360303005000d4901d0544c0c103000402c80001c1203c004180c81203402c010f02e03211884103d05483e01500c0c003042e107039216044000c0070807019500610300c0b02103400c1021407075030228403101a50a181d0328461107842400044500107000c4c001c0c03000e03c450b00c1010404101c3c0b030403c071500382c4030315903030b043e003011031a80319250603446c2103640702843c03d400400c1044c140391085800511540c2400d105281440400d41640711115420800003441800580ca88030821102e000b001c0708150100185a00d002009001199070001d0744001d822505050000c82c0c5d51034102034010503500350340d4900b420140745480e0a00c9002010007080252a401c11200b0304004080c050402c404900542405000d41c3d0380c60300c0c1d41410000020307840442c035500c11038919a5504040d80c09 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 762363965 1250 762362715 762362723
    0x2120304061d1203120603060a14010b03040204110703020c010f03091110020c120307150e060a0f090b0403081f05210106090c0815010c12110106030203030318012403 73
    0x144400c001c0082100041c03000f8801e5038921021428041c2d03c1103c889081c4603040c15025288903458800c9a00d00f03803104401c50b414010403540051000d45d41d90b00c05158420b000410205040f1504200603003c0d03884039034190700603000a0784001040d41c000000c0f0141c50b2583ca010000400607841d0002b075201e5074a005480b1303c01c44280c0b030740b1441c401c00c00145901c100030006469981d05c0800d040e83d90303011030022180700381c5012045040300240e2040084103a075500140c126641c84108040007440c80548840704030750759444a90208909020146c86680310b501c4802403800d01403003441105a107650740c071601c9031410600740030b180c580c4c810121040c15500c019804880000c41d41703d016158907004402480d01c2c014180d610309500000b4913000d06018070200c940600c680004482c6e0ba940610701420381c20007040f659144501c070b0b070014a0340d44621800000c0d00350b22580000e04650081c0d6401d504e0f0302d62410342004070b1030203100c2c040c01d07100d800b94041024040300181c0030328075185102c050 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 762365215 1250 762363965 762364007
    0x4080403140a060203072c100c03091509320112020f0f1c020309120c01021605010e0f1504080307170109020703030b0402030402150f160b040212030406 67
    0x5075140c8104401d1040ea640101c055450340341002000389038a50003081071a004900c9110718500c001940c1d800c121202c00a0612180c0d03140551003a2126669680218100304a924000449041041c44184c88103d0f0782d80f140c0d80c2c0d62500f242100200e00300b2903201c007588181814080c0403003220201550a007030030b0800000054180488000070301a00d04500041c00000500030341c51081034004003000802402101c1e0880300408840c000c81c041101d082c20b0f01d9002e00080f9845645680c013034550b407060030001500d0402c140301580008810071400326250387d12050882a4007409110a050071a001c0004010003284050000d08004014101070300c00480040800c190078440c40620460010010b0000215650390b00e2060003580300103400e400003450104d100445d80307464001c583c000c80e00100342000084010440040f6a032107000496006041008981c00c40350b10242010001c0b401404510054031303140c0140084c80711a43c030410b403160406c202c00c1c80015001503d1a030102c602905078 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 762366465 1250 762365215 762365243
    0x17011e061d120c19030b06060f0c0d0e0a090b03060c030a090f0305090112050906190221010302031009021503090c0603040b070e061602060309240a060b0304080403 72
    0x4078002640c60401d082e00800b003460101d040480001c0c0c4000c00d0340c4143c610503d64900f4a08004d81c50a01e400010569011074021540d2460a00054103242c103058090340c1ca80941c08941c0e510f030102988a01011034003a59443d00ca520b40203100c3c6000b04400c0c0f806102c0e1140d10800030b0380f1048010a541c04458020003c0780c1e05c5001640081501a407105071004407415604010300305c0d070040c0c0082400200342107214001c03014640501030040080000a02d401d845041003005011860244d0a02c0c0c02c0c3e003031010030101c40b801218000100344017500c40e8069415030040c0f5042c490340c20800c850903800c00c03103900b0058554035012107000904a0802d601d179111445e105083c00c0030f40c0c5102c0e501c104040b050209014001100c64020045074440707072050121102804401c1c010000c0700c500025003200e0762409401c0201c01103500507400c03020f88411800007411002012141c0d0007a41c1d45502e14400c225442c3d003581310340320280405402ca281585030560f2001114400c0b800000d0421f4a100c141d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 762367715 1250 762366465 762366497
    0x101a0424080303180c09040201050912010203190f090c0605070809040f0219031b2001060b0403021c0c0302130f0515011808060f0615040617011e06 65
    0xd4204622024680d0062540d50038029607290019140d61030f032441d4038501380d81c10403000191099a1000900380384410303a140d400554040d004402d0140d0040348107001d89400715000e00c0218071034100c0c3e04880c00405944d04100045918410008802920301180800419414442041160450301c1d0044e505c01d02482d00c0038203402045c0405800a0a041c0d80364503140c40c54010b4103484440e041c00d003054074005d000031420760340c000421180601e8029040c00c01c2500c41c92002c42080007100d40601e0f0214030b20030542c210f4045600071160040081414400c42c80c011030416100d00503800480103001d241c0e1102c1c20f1503605440700910038002c6051409888849400296989078000e504020524048c20718021014005415a00082401014036041c2c1c21506e1003038180c0303035643c0c005c1180780c1e502240382c0c0c902c2c680070b051103034424002c071164100c400e0110028406450705030782e0b0311251b07450401d0410081c90180c10030b040d4030b6800401e6207088000c0e50034501c11940140f404182030102001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 762368965 1250 762367715 762367751
    0x120702010c0b13021f080601050c0708062508012102011e080105041118040e0109080a11010c09120303051513140603010c0c060b01050d091103101a04 66
    0x60042c0b10031008000c00003603900705a07507101e0ba580280c50212402c2c00400604003024541040140410100c501059241d41b040000e000c034121510215810030340c0302c00e4100e00c0c250046988905808408110860701c4000714142c20304401d19081001165041c01e0340c0c0c3c4d1420300b42020940d40b05000400400035688106c956135208102c00725049a200c0d240c600003061394909010301400b860404120016080084c021281402001c0500004d583c0200040001070110303041014500c1d902c4600c2e0201240c149001410942c02d55100d216400f100c03844941d0035a845c2a07460002c4c40705581d000c000c5500000b910590f80c40e0702d07140c002465501c0c0814201c070303003c60401c055000121070185043c0e4205aa001802000d1301078000400c0e80e540e001010700383d58036070696800041d1804101c1000502c0c80d00498400f08050401d00d00b8001d20b90888400c945140600313031000300b040c40ca225602c0c10140107141d0300d501c0c602c006206070f02910b44c800640c4a010382e10503004031341c2c03400e0209910880704 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 762370215 1250 762368965 762368987
    0x80307020a120f170618040f080a0c05100510051201151d1b040e09010e010c030c180e0c16050a0503071a0f01270e1609020c12070201 59
    0x280c0050300512007600d00502c02d00c03c20001c5808580c0d0003d031040c1400000303034141c2c4114130040c000c85403505d52000c0e4507940d0002038001c840d02a1154582d8000a269a01904603409956075400300c080407820014500070319030182d070039000d107401c0c1403000b80c2800442500907182c0503260700040301014042d4600401080c001110003407206140811b450b180c03d0104142541481031002440e29013074502c0c0b03441d107607410b44441d0340b04040000b00409582c4504503580082d20800005608140301003540c2915900001140000d41c2d034402d01d06c0c803c2d049208aa6600c20f512802c642c01400c00d080c0c0c0441c0e40d00501182854040426510441100d05010260055000d0141c600301032852620540d00d4221071001c50f2a0000c88030751220040c1892050b138841d5040c01030018403a461f0020499038080740000205203107095050744032000b0300b140102c00138a9140401083c02445620b81100e00c0700b0141c00c442c1c5558010011480100c0e00040c1000114140c1240d541c3d851045d840141ca40707418030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 762371465 1250 762370215 762370223
    0xc030904140702010c0518010c0201020304080a0609120509100e2107060905031b01051305120a1511090f030a0203060a050a0c05090904061a06070c17010204030c03080307020a 77
    0x14611801c04407a224075400741840360000c0c44940c150b010709548034002d01c0661401c240040038200b240790310a900583c485070043c01a0b03032925403280001410b00100d4071095800c2912603500340d04214001c2009410358002e8500b00c1c0c100520f100000c4c602c81e40504111003042002e800801e003a0f40e400d0340c40f0305520398001d0000307c40315090321500e80783c0c000751154202250003078400042504020500080740e500c001900b44c017404111005541f580c0210b0111141c1034107038030020600780c90742081c81d06590f01480041119081d0751a2110070400c46a62038420b450900302d1203000929500c007614140307481140c020b103030700c0724904c0030900d490080400654544512810312010303106603403020b80030b00308041050045408080d01500c01e44242c1c4500c40c3c22409000c00100818410703480100b10105408000500c0c01c000400182683c214000c2070741c0050111900b0412050b000d002c0440e0140000000d604080c030750f440c0c41c405c0300064803000c0c0c5500d00020010340d000b03100744640d062003a40 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 762372715 1250 762371465 762371471
    0xe010503010803160c0b2209140c0706020f0408100506010f0e040e0a050105072007031a07110d0f0806041a01051803010501030f14212a061009050f0402060c030904 72
    0x2115200040c094001000c14100c50400000400c3c81d40c2d050050780e540c8140464051349c1c9403501000d4800340c5d8860002503403142e17400e00c81d024860400000802c010101580204003a41d81520100201c0d10b01402241c10300042c0c1c406180d4554000389400b85d2100200d900244440700b003a500e038100a5284401021540b03042e08200816811400813540c1142c3c07206190381141440416030307030721002d900000c0c0c0083c0010f0082c804c002022103140754007607480c0c80d140c1c000040f003110140c5031002c00030466011921450304403182940c441071196120100311001d11081d40a201410006440e0048580c100b200004805001c002003802e64140302d64040d0007000f440d80c5d2414110881d0b485c05000316424040000058036541c3c000540841c0302c3c0940342600031189039080c81c100345034800d561004103420146813040d4180d428100c00081c62010101400320b030304d0404c9129206a646030071004200d031a000c248003e818643e000590b1081c1e054135059a0742c49400021442c6002c2e03160007552280c2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 762373965 1250 762372715 762372727
    0x6040c17071107050d0b090d05070506060f0103150305061819141608011b0807080f270d030c11060403050304020d060903030902010f02010b01020a0206090a0e090106060e010503010803160c0b 84
    0x10152009a21510400c41070b03070051201d07022304541c28410f02d83c01a03c594030060210b00310b441d2480d181c10b00a101410b0014030301400d41d00c102c0180d1074a40c003d0301c0540001e0100208444000080444141c3c940050011003c0102a07449a0b0401490141001c001180098203a0700e0401011000c80d81c407007640c0046c9a0750740301c91400303840c00c01c0d000343c2c040d80c2003441015a1400b0b00700490098000f40c8030304025584001521401c041d00411120200340d00905034034140b039859007900c001c440704001070022458644030160036250204690000c0184040345420303002804200d440e08980d041c60a95900d441c2ca000050807504455030180259113004a8102015010360082031014800e8236020f0300b11303447ca60103a08980d4041c01182c0540c01c801c60070b030010f140620081c58a54030041c9407110003500c6a411030004001256040d5241c1e554503800c0c001d040d00711240e4650039109182880c650340c1422005a00d9005005c01201030600800800e001c01c0712003280b6001512050700e225490311 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 762375215 1250 762373965 762373973
    0x1202180307090e37060f09030801080d0804020102033702160501080105030a03030f150602070618030c05040510031e11040228120501060806040c17071107050d 70
    0x8042c10107503a50604c240b482c81941d10000c0180d0009000031003440046003a065209510450050780f03040f2252075503942a02d6030011a40f00308246d1300e00030361343c540782581010101c0e4500001800803109209440c2d04200060703a0010841d506030b081c2c00340042d43c40e80381c007480140d20f01240ca5031134969181c5550b081c0403180e000850340c00f41007800c030116180d1641d900c01514818070a0059a4042e044900c10b9400b1070b010360054801c2100210b000100f09003081d80c40000315030345401620051300b20b10000c000712540075144105441004000b000c0162840e5a0410130034228400c490286e034503800010302c8580340c010700c1d20055811500516258101000e84d02012082d00c204440c11200b42c8480044d80c1000d1007030301c050b08083c0c214490451b070a40004c690b04201c410b003080030001d2801301000380144c1806018001d196640781e040d10b03402d142d0200415100c0e07403408001003000200c0d205560855182000781c108050b41002c404d8000c084440d141420241d400c002e80107450420400100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 762376465 1250 762375215 762375221
    0x30403060519500105031b180c0706060e1b040503030301030206130b0f1c0902030d0f05070b0c040f0f0b0703080c07020913060615120218030709 64
    0xa064050300d80741c80e00e8101a18042122088031507a1548a0001c18801c50600c8006907407800b4800e030110108200301c1922a95400d03205078540c48200d03d03443c40100843c1c2010030140041c808a40d280c5418401841d010402105850448a5441c0300600c0850f1581248400703d621450f000350b800d00166480d00000448140160ba04038a1642e40000748a00d80c010b030350036078054510080180d03103540d184d90201300f0141c01056100454221482c0c0024024084000814184061007240c0e0349441c030b41942c40501004c800003c9040c141003910b15001a41c0114a10107442d00764102582d0075594402e04032014041d00f0700c0100442c60403424440908d000a01034000c4a5603200c1034a4059200c650154243c82d642c07003061400303d401e121050000303000340001640b0048032940541489690740004011003019180310001c5928403403441c0502950707014140c00380003041c0308103c0d04d4452039001400d01e6041000414015404243d111481079404500030301483d005041714543d548900c452801 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 762377715 1250 762376465 762376471
    0x20d030206180304030507331d010c0203030319020c0a050106031110090e04060b060406050306040b04020c0c04090614090609010501210f03020f0615121b0d140304030605 75
    0x2404000c0c42c420320b50301d01c1c004225420340382d004002d808500d01d88a000751144a07202c0007201d15000190000745210202110855405501d0380c0d5040c284000c02c07070f988a180060750714541048105600d100158130000201c80d089041310604100383e60030303408080020700078946882c1d200d004003144003050000c1500400190f90040005481c20b00c080c3c400c0011955054130b02c240402e0028801700440e6842080440e4000d000314004120302c45100c0005007544d01903040740002c00d1001c0280007040c00c042c828003a80c05000d503030451500d14982040c80e5980d07400c0300c8561082e515100443c003001101e0300110601a04199030b6050b0f82460045d1030b440f4001290703248915807030400000b402480c22080344c1c00c1a0005512880c074400c440c0c891072844010000140c06502c98064050410304040040c14420102d0080201519801004101c03020900b000003c070b41d03510110740b03401c0035085050345000d414070449000282602c94a003424079294456082041e50001181c00130a100d09500030900c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 762378965 1250 762377715 762377731
    0xf0a050a08070503120921030405090a0f0b030a1e030c060219080703020a0e010f1701140a0e0f06040905160602010504110d0f03030507120905010c02010e0a080304120507020d030206 80
    0x1210417046940101e80303001d9038902c29030141302e090025241c1408051844454000a02503d00d00754941c2c011510300132040e1001d11010f503807600c44907825420b9106151400304200c010b0800c08200c0d480b004006c07800e690f8562002d604035101070301010700550031a0702e00b50380b008041d5140c040d11028100180c02d450002c03000310740b03481c0004016610034070896407001515150f1406ea906450700444008403400d9014080c0101640b0848182c580d06000e18020b1801035960141c101410b003d112000c12264082c021a10f1a4828881d01c207003442072044d44600c003500c0c0050440e0392030401c28030b0304020500302c212505100c04003107401076043d00100d1003280200111182c2a0074582031094000110402404a103070200b20b40780000e2103908240d40112051810401440c08804507400b1240300718408c8450740e645444410742160280900a0303550210b00107800e1850300780d03e03102c0701d6100007000107004104480d41c0c410058021001d50342074039009801220b1114003484c0c065540c40090b01c45c40 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 762380215 1250 762378965 762378973
    0x317090c03150702010c050403052a0402070606061b080301150512040803010515070f02040903110f15070201111602040f050c1b010c120b04270b0c03060d020f0a050a08070503 77
    0x40000ca010b007089600300c035841401022f0000711b1000f0140490303140c082d00180140c140f405e01d480c0e5562400508015401000c0005116182c42c00140c003404c0165566034038442111400004104400140d030704582c1070f5003810500d81c40e136800440d4a031107212401c403907194184052000f80711018003e9410789a0985900061b6003610020442500034041c00900040c440d800c50001824583c21810b8100c0c0b0070300f01024290410b03c0300c5810701c00300d02c1400780326901040b000d402440d04882e2543c0c200071140001c0004841041034082c2921400b01c3c21510422600441011910740703522011810840000401807400d22180c210440e512220208580d04443c9110f82c0c000c41e07061246d200520300585a0034280075095000c0c0c406003c0c006091684140c0d0746841002c5003603880006111148801030311220318031a440e100480e000050b01c0026211000d00822120352148134550b81801c1c2c0407107071000300140c21000034032a40c20721b40099400040d89100010350150015000d800d40d0784c11420b80d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 762381465 1250 762380215 762380231
    0xe1e07061101060b18182406181207031a0402120d08180a06020f0310060806030601030305070516140f09060604170a1407090501060c0317090c0315070201 68
    0xd9400d0303401500624041c42d404102c130584d0f0745c001003422503240c0c10180800551054405c0c040c611840101d80c1000b119188091001242034008201000f0f100226101814012131800c0c0c0007141400d0f2250a004510648101402000030495a4011503000303c10261031b58400a144031200c0707058500301d0007541c1943c0c0c0907000c030030302060906110105664080d250342e1240000c0d1100d0309025800031044c050700ca9a4030200d100c4c3e0004003460350292403401e17038a0500403035101407146036070f0003103041242034030030b11982d5034010a83c24110b0307801d86060390322040fa90601d241040001d25211000c02c1c0d05460010340d14520007084024180110f445030107100ca00d1041c00070000c1c0807100c55900134810841070149280820444070241700c00000c54200d622a0342d02e114510b1079543d0740c082243d121110410410700203028417809441d00d440e2003034400040d42c5d40a8a8107c1b25046c45078030030701e000000b50a142c4208140c024240e4010b007201d4590702c00d100d00540c0c0c41001d0b1101401542030080e1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 762382715 1250 762381465 762381497
    0x261819020a05060732070902090f060a0503040f08091804020a1409010902130803130e16020a06050601210509011401062010062c06060403060e1e0706 66
    0x3036810243e088407481034035803403145c64003c0200d00d10342034151034181103083e400040c0c0e04100e44409082c9141c401a501c01709101008803031010350060910507402008000145030340042501c2e0042e91250036050401c40518081009010749004e940e0040c8400c15640079552007a540c1500440c0242c40160001c0d07103d60340380c016141d09102e102d070402080030040119105990042103010140c0c9100c0707280e1a16010307210b04603440b5110201030a900c0c43c0007804034110344040d85800c401000a01f2080c11800034020f500c46080010140802d60b442c800900b450340100368014480100801030308010356150049c0c07000f018180d807007404a62078500400d0600400170030141c10307140c0584640303040304c01e0b080d60202031b00144d040501d01801030b0038002e02ca00615000e100041c000c5944003803140800604440540020003d4240354260300780203001c0c60f40c07030f1801213034242d9410081c0030880700e18495440d441c100030170703034001c4c4420380d074861039034040d600401c107542514ac16032740d0415841201c0030303 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 762383965 1250 762382715 762382717
    0x4110d0e0106080a242c060f0a021e0a02030a0912020f19120f0b07020703020f0f0d0f05030702120604021f020a0204060608100501261819020a0506 65
    0x70600380d58403c000d2003001c205070791a01105010000d4078240c601040c4e85d680760554255003c04040101100c1c0c0c2c1c0041d0a0003e074100d8810307040c48004000d00d240c0104c54414828000c2c1c140a141d6a00241003000185000750402c40b4074203844120b03541c4c2595010080d500c0e4400c409150024440305008a40a04410b00015611303400810b1a0520380780d40d0300f00a154103401030084592484500c000600c0e2000c01c040c80c06081c060030184500714843d0a0044014070024403840440d0080c3d5000d0005035141041c001c6051000c0d1031034010181081c000c103c42140c803400103080011a104981c080140010041800d548241e411840301c40d076a104080c1e0743d110aa030001d40c4542ea100c0080702103900d0014a0001d1800c0e48111055080c10360080780441303019801500c000b91400c070411500380c03940030003a0001c2c102032030181080d052040c46000d141a1050354480c80d03800701c40c0803642c1c40381075801e04083c0d1039402e8180e0b040c900107030311700507682c0311409012405417400345000a10781ca0100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 762385215 1250 762383965 762383969
    0xc020102010f330b1801021606020c0a0e0906070302090a030218060312031b0d1407080a0b03070b040306201b2b0e01210501091a01020a0605070e04110d0e0106 70
    0x84d4110300784901c0e11185481521844c031840e0451240f0b040b92000b840f0140c101e2002018107401411102104106110b6014800d4007c1d00d5158516000d00c41e50420000e030540e409980c901d001a10341c04081e001508605583d40084d51089004210790152610252914001c0c1c204034100c0d01c444402c46002d14075400f0880704544880001c191001606001e41c3c02850904554039002460b8803c00020440d001001d03548d00c00015001001c0225107680d5114412209108500502d0310070701c1e14000b10300e244160300000303100035212075002040c610794102d41060000c454040603140c0307401c2010800031a01c5200e001c0e101d84a091403540c0302000c4540e11291810448000013210030309120207441d04601c81920034100204e4410784090110b012a5284490070311820128080d403415810700b0550f01c11080300c0400c04510707280c0004d10ba8001940880c0340e90300520204642e9209041950301040744076050740c003e41401c0d00442501000c0000300307102e403004503007002080416031010342241c02c18 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 762386465 1250 762385215 762385229
    0x2030a0c09081f0623030601061b03110c09160305060f010c1407051c02030601080d0c0318080a060f0c03050108121c0e1e06070f0c020102010f33 64
    0x410341c0d10030300e0980c040210311108044a8045944e80d5100003807520000d403061080350381c07510758280148900d002d0044134014141868060540640d28015803001c0c01c1260004003804900c2e0000c0450100510071820540802046207180f49401d601d100c24244140010100203032500001601c80c2c03600301200d9183d00c00c181e41d203850000041d611000c00c12440c03484400c0512596100054940d12002c000c00920042040c8070110046841814a07009040c0c00104664100e1840c00380007aa01c4a50103540c19010701c0c1c0280296961a0307014040c0c02c841e08413406d40d01580440000f03008080e00940045600e4007020084840380303a2045007142c50a00911425800016400d80307901044c0c0040c041240707061b032104001c1c3c01e0800002046414005080c03100b038000c10021001010a040d200c01c0ca03030424009081c0d9403400c040020b01a500b501c1010b0248580034003a1025a4400d5100b100510700c004001c10000c18001420862468182181120030035440340100104072544045411a011 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 762387715 1250 762386465 762386473
    0x40c0c0b0106140403080f07020901141305130209040f08040803190201021c020921010c0219121d04020a02061005040b090f04110319030f080103110f0415060302030a0c0908 76
    0x565803121600d50000d1f04666400e28240f0207880542c1d00c1e00002402401c9900c408103560406900384188480b400c52071a4800380390404006014422000300910640c0c1115502240d50b603a14084c1c419500c1010054170340c0c80c000c5004110200c0c00001002c003403603204101000c41c1c1181008900381e02c15400990766950490820803001c011a0300a8101c0c1703000209403030802e0409120079000b241510921b40714503915440e0441c3c03069014032607030303922030308030300990b050f07000640c441c1c400c1302041c0082a410460140200d01040104030b04906074190014400d41d43d03000c0481000f0740d80c1c85c040d105800380c3c101c55500040c1c07602d41881000023a200140c403c07245603499501c061070803140108242d468109400368420165414851410003542c01021101108481c0c00e00071302c540e410b0600082070081c010010710210b01d4a525241e90075408861880c0b1132951040460301500c90044010240d5a10340c2c0e003c1086070301500a03520070070800101f00200c081c0f002c0c0441e8184120700c1800c2c50343d08 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 762388965 1250 762387715 762387719
    0x403121a010f03090302010b060a020c09011a040e0a200306150319020315030703081903061d041a10031118073618050103020f011d040c0c0b01061404 66
    0x10080c4c116000030750190000158910b501c0000c510990704c084c100000581110401c140c85103401102113001d046000305003903104444081403901841240144440d00301e0100010b500401c090b04120a10301e10301d00d0440040412032028542600306480e094480c840031075202c0e003d114182c05981c0700d03100140c1c40406905000405000070350006c1e141180f000080c2c0c1c8150025181080844002c520030704a0329944c005109000044101d090070300700130541004c50400203e5601407401110001104a900e0545c4403881c2c50049940c03806508000322051400304030151021840c41412039002d0244100814a00810002300090604444580300c02800205594a02c5980c204074610508000382400e881d04214040210f07201410407007401c076003c3c4062141c58004400e2100c09050f034501480b09505503400640d4400c4040e0140f810000a500b1100320700048003904e100c4008080e10070002080880801844141d0001d015128400e406000051551080010b074218409100c9903a05049c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 762390215 1250 762388965 762388967
    0x11150a0e1f020a140705010c1203140f010503010e01090b07081008011a120d12020307090509100312080907060507020103060b03250c080d02031e0403121a010f 70
    0xa480c406003035080003108801ca035000000e5405480d00ea1515001000c0035007661410318582040b50f07494101a400051080102da6040785a402c02d50781c0c000000c0314aa0101d04c011002488400b0840400c242c0c54424800e2500b54520040d05940f01a002442481c2103002010300382c40c0f00c50402400c46c222040001d03215441807515a4000c101500c030000095a544106420340d1440008503205011041049805107410070f480d80b0141c5184014050150f58002c0103042e481150900101c04c41d00000000d000074403901644001e800014247c50aa0600d090f1445158460340001c855201c2d1004102212a018031005407207050801d0040c041c40e420410100d8094120329822414141c44910200b21915200040c5101d00c0b0010101e820220166480d20b24072000b590783c9a05100e11451000007249260007107462603400343d0310159803a22164240b20010300600d00031016403100354140010507a0100700030b1035411080005020701d001d25810120050b024208150119001050b088402 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 762391465 1250 762390215 762390227
    0x6070b0705040b070b060307061718010605040f140c030f04030f1b030206060f060406120525021e16050108070c0203071d0901050601050307050d23010311150a 70
    0x9885142a03410070380e9490f9410000c1c3c0110808a03054401e03101040790a04081010743c0081c5030b5860030000142841428104151024001d00f4503074941d080d459035881c100750450401844090030800000445829840c01400d480a002425000e4074011803c22011203054034001d41319a100204241c0340c9507826120a81c20418410a219000d41c8035901c0c15a010070180305680a90044c040c1461b10703500700704020540319600ca1154100b40018803446500c0b6008ac2858110500000380540b01c550b001c04190207034005012810b4041079000c0d031006e0740424247c0c0c206003210034462144901034140d5480e134815840b00306850010341002c020a6214000941e082020b83c02c10785800407042c0c0101e410800540c02202603010b458581c0c172035400051403410751020018000300541d04010b03000800c144006800c0030200040030030000401d00099110b02d03052011075900c1c01c0341c500d24503140c40d11440e092109581c0c6459901e0340500d40d0070842c0008c007001d0800303000b02c0d16101440c2c00c140c2d89 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 762392715 1250 762391465 762391471
    0xb030106091503060b04120b1e180c060c0c0901080102120601050f0d0c0905030c181303090807080a031209150e0102040b0c0c030f1204030222231506070b 68
    0x405440d00c00018091030480e0080c00a4001c012107004c0d86d800c0ca0503c50349030b0201809105009c2e900c030001846003500301500030b03000b8911400c0d50503207a900a0b24503240545801c2400d41c03002002810f8510720400203021a200001500c1c003841d01d80c1c0c0c9160007402c07030040c1086100801d015100003080343d841080249074464486c0d501609103008118808112158500d110020078109101880302d8034003000002c8032140b0407101c000c00d12162030031400c00c0c0380014042c040070760300310000c071010140911b00000141200500f00c40a00b42e4580380b16541d440300c00703001d0700880d0780d40d4502c1c5d4001106000e1080d0b203035007084814850040040040004000150410307820355802e100100300c4105840c02000030841c46c4004090f03007001c40301018202a400d81d80407107298029000c4c404035000d95810394040b650100c035042401260362000740c28684010444070303940d40c40c02e041e00c1040220010952280d1040000c815015603440c401c000300340030f9100520b5400a010f01c401c0b400242d8071000340341c1c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 762393965 1250 762392715 762392717
    0x1407050a0e060423012a0f030e120a0c05060f09120f0a05061906050307171608030c0f16091104050a0608190c080f06010309081603020105010b0301060915 68
    0x40b07855640c00c82580c0b5150500c00c0d000f4030700c080341c084015a40c0d00c0b101e0700a03c00d021520f00703040b081103031086c500308000c01c02d0700400b100942c61008090600a1240004152004c2c00440350180810300c0b040e03c4070300b0980c04480f000700005001c40d0505100b0305480d8200c800b180030614010300c2400704058042c04194080c40340c800d51002448044052003507260803440b0b240102141d042000c1041c060081d01e4004118151400e84d08000550340041d45000700c40c00c48800cbc50805988410090070654a40490000c0b5850b50000081140d0300200400c2c072201940b055401c02c1c0c001440d8161a1803420000e2030302500c41e0a000c4c08050020341c040c080c1030081e0203505152a6803040842c400004503440303000030031501e004002802a1000c011114180e080e181000361706d24608010b03108403805404101a80e106500042469029a01440c8081e03000182c0c15152640401c0c0d40030b00c1010343c20300300c0055092500004203607102000f030328142d40e1280c507464900c0b03040104c229409158102114 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 762395215 1250 762393965 762393967
    0x60c180910090c030b011e0c230607050909070306030b150316090204050117040308011413110d060806060603162003070215120a0507031103100302041407050a0e06 72
    0x1035502c180d8455a0721640041e200854600204000505002056815505c3d0f5a000441c0710555a80c40148000020384c05200c060b0320303d1110b081c52a40000040907507215210ba0780130f21502d16003000190a0700030b000c03200d921a6a448600c00c03010380d00c407803100814100721078010858a820381c0f2408c1e0150500901190075041900781d1020021000703603c220740b243c0e40000c062000f96808002104a4000b5110065650520340e800070140801441a0b03d00e8500c40842c0d40155641d0918800000e0a1b2a40030702509107201446610342d80310820f1864100c0c540034001500301d00102c0d520380b003142e000709417074190384d9807460001c0c05154241004080154041e60464100141b17036050703141c046e8050085460324000c1c030500003078103059500310041a600780040d070f141d04248400c160344400200c5021a141d11105015000b510420482040e15500401040586030640640b903003168000c0360107220002900c140e102940505032240e00c00920f040041c4030312117020790f0361700004200c003600003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 762396465 1250 762395215 762395219
    0x70f0611090a03060e0616090603020307030608030706060e01120203060a11090d1209140904140309060d090606120305030a24081005070e0d140a020a1205060c180910 73
    0x103020310b4a5400403100c0580c0d40d01c0340a41d1007420020968060305800300302d10005581d02014145c0c46c010b01c2107000300350700040002c01c01d030711035080f1100500343c26084a4584c011468200098201c034003540e00408043c0000140c0440c8050b04c2c0706141e0703005006001c440d1200301001019003200b04903005540000c202114082d00c43c480007082c6907024282c0f22008030200d4000070059a0680d1102c0e1040142160101040d0384840f5410f8005500010000711207082600b41c40c2035000d0700706101d80c0301070b01080c050740305600c5800030000c503031043c1c0c820051544c4411245611100545000e000101c1c1800001e007180c4444d40480c902c2500038400c03040c482840c0032140c81c044903941040410340c000d0074040000f0041801100d0f0480d445091984046000e08041402622443c070b02401410441c03060003400c0d942405010243c41c0c024205502e03150715510341c0c00a04a60080854140c1f00304400504546554030548408005007400165446005810411081c038040c0600902d080030442c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 762397715 1250 762396465 762396469
    0x40b180603090604060f020304031409040906020c1e0f0c1e0301180506090609030d151703040f060305010b03010905090f0609010b01091a0d110c071d0705070f061109 73
    0x614802c806402c01031480380f41c1071030b240003a42c54150318000c1042c0184180400260011034019030561300b0f444507611007001d24000b4028020404025108a10015409208000206c1e05502207030021081c1019903050844a9980d103981035802d513195007002c040003040b464078040c8281c80380c04c2030386100446c400201c0020b00715403142c004080c0e01e00302c801140c02003120510281c1e5010800001038191845d01290240c1c9a01c42d0383c80c00b250090383c0320900340002922014101c040c10554000c458080e0ba0002156903c1c1e000f4051203e09900c0e03034400040a611034000c00f41a00c0c00320142c01d0841c0d1038038000e84083c11003e003484403c0e02409080784010301c1d04100e041e1240b007005002007109444540054143e1505d608034540b41c3e424410180d510780800380c02c49100d040e44040004082500a56403003060041d071001508034090868000b542d414545e05240400c552540f550f00241c5a9074810780baa8130a90800030110581d1001d0400031072000e0b806048800501c0c1011442c007180800 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 762398965 1250 762397715 762397717
    0xf1b040e0903030105091302030a0209100306180506010e0112062a0c02040501150c0b0403020a050a0503030109050109270203010f0e06191103150f0405190c14040b1806 74
    0x540905180e00203c010442850105a02030704045040c03e81c110604554011039101c1a0480e8081e010344a48008a51410142101500290381118040290207501c0b0b11480304181c0c441d0b01520f4910440e0008188030700713604843c1d4103d03141d00c101d200180d50560b0f264000740c0507404600102e40c47c08105403244a1800860080800030769444e9014404148100021110f060f000307084101e4041034001c002c1da8101900751107203500324005000c155501d00c0d0403460540c500800600c0750081920071001c2200000146040e00c0c03080b0424800740c0c0c0c03600600f5040317540b50303403601030300400d0710846000d1801c011141158940c005000410010110483c403026540309a440c0c40d5640d02c9181001b10380010303044111488110507000341714582c07060300800c1e000c2c04080c215092010560410010b0343c0e45e50400c2a401c504098400e021700e14140602c9404040d03080e04d4040458282242c08000c0b5105401c119016015100c815040c207080801000203500250603011a110081c00f41150715900d00e4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 762400215 1250 762398965 762398971
    0x60301090804120212010203090a0305070c080a1407091e09031112090901150e13021c020a021606051e041a0406140c030a050730020d02060f1b040e 65
    0xa42454810003c034414403403100102041501180d00c148240200d03204041801209150186072035034403100306041002e280ca0140e8030408051107007001c40810083c4044c02403007031610110960311590781d00d0085400381e81c100740d051105441c060980c0e0140704183c1d8000050b0303600a180803862202031000c03091420641c1313100850707a146e002c1801c01c03c52a00e00012405010700e9501e0001180a5400103131501d610b03400c251340304000740c80742031144250b01d6050310703c81c221902202001c01c0a29000030002d500061900300103029400128070003c106141060888116607511460083c0c400c07074014405403654440304d01d10400304070024003c010f4a00099081040e0f0600310f940320f20b4040094001d008030752407024002400d0203114070034000481a1a102030a030305080341d8407112468198800b4a8003581c13071524042056071000d00318407038921a8180d00040d02203c0308014004411303641ea1130110f40d0344860251145c002410305201c0d07450781c001c07156854801707414180c81d0480424001012 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 762401465 1250 762400215 762400229
    0x19060c080f12040b09010c0212030c160515010f05100c0210030603020303032403070b180a090e0d08282a18050d110405070504180605130507020d08060301090804 71
    0x4d541407007520042845401000c9001d4002005001c045001080041c0402000c0c00c20405000c5500700209044141e02e40d200303603020701a180204e440b40103540001c5028081e5100003020030101060900f006548092210350941314075000e40070660070003a828081403805002c041d1940c0000ac01610100041c6000340d42c208a2803d030141c0c4000e400c646041600c1009101382c2c401c0d5800c00c80514120100d9003c00500b502400d9442031400c00715038124583d03800f0101c164a48402d0b40301e1303c2404130300100b100265941e1120281c40320340c3c00281c07030b0f103a50355284100b80b2006c1010203100380c5603104001c402429012004590b41ca1010715040141c252050008034051007c00301b0103001d040100d802910085803c42a40a059182d0481c5068000c0035180150350703071703000b04140c14082c00680c0e0092000e1503089000e02d10180710700340078110500c100e9008900c014640d40a000c00e602811788500c0b01c2d40d00030305c10341c1c009040840d5001c1001d044160155a50f01d03200021440c4e5000802c003410381 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 762402715 1250 762401465 762401483
    0x1a060f0409060e06070c030f2a06021801051c15080307030c1131060f060201060f050409051203040807120f1e0203180103270219060c080f1204 63
    0x11100f04a0070110003c0504c0e080000d00c1803107600203034000010860b5409545007400074044a90751540000c50103440380c0d030424503202204400c0012071f4000b410781110541e0006240c1208500540c1d06000d080044510492450280c07000750300c20742c0c071100e02e8451a48024100d180d480c0c15003800e540c800700e019000514501941001d0266840307810030700900030744184600203401010306400c01c4000308007880290500c80c410020315038035000000a804c09402d016800c554a20f0046c1c000c189030f12802144c60072081300004c00b460301c1d11134a00036a40000c06403010100c4011f500c65241e000500880b6020b0b800d00111010540c582c000100f8100162102c0c1540002c4e10070180c691444c07a50b90b91800c0606060550080360b02100340c0303050503022664280455400c5005901a104604510841200810702e00309450b41414500c0c01240c02510b41c0004138104105a1202c48043c3c0220004207100c07119003c0005c050030010110550458201800c000c0650507151140e00d0640d0140c0c0d441340 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 762403965 1250 762402715 762402731
    0xc021507060b0a080c090406020903240106021513080f070c090209120105060a0e100803030a0c030c0f020c10030b0d03020c030c04020a0c141f0203160c1a060f040906 73
    0x80c4038440201800130030008103440e810100c0040c0c200003004200510494000c251209507071000c000e00c1c0d8501014800c48041c6081010740d5850013030702441840700603c0703040c0c03080b1440826480c40c0d038050030301c0e01e41d0600626423a40342c41c42c00f648109107010b0100d000300300c24408075a01f0318102d0058138a20302c001d0b0703640140e43c0030001e841590300001c0c03042d640f602c0d05020440c0e44120980d8210b405110039001e0694032802c400e000f1212541c0404564040001042007084642c4e0158101c240340362000c00100c07030b0742c9408032422251241c1d1400507a00c040072f81082c41c9040d58120130700700520300d004035920b0f4080380490121407100b201103002d60310209400d9042d10701404903456204c002c0e2411810300010b0340001f0900003543d480a0110008180907121030b590601040c0340040380c0300b6201e440345100f07003a4500298400c8402c140200042400f5249a900c5030049402c00d581109004480059120344240c1c01d02c4c001d40304070b40c0030705d480d040c903289600d072800340c0e100d158010310b8002000342c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 762405215 1250 762403965 762403969
    0x1520030c1312050a05150717060a090e1c050a081807090207030809010c051c020903010e0a0c0e0105010201020a080a0e0a0501061509080d0c0b0a2003062e0c021507060b 74
    0xca0381c482140240003405040050f01e0360b001c0016410070342c088e0540d018a840c1d0318045030009640f80c022606c0385007030070141101d0000001c1c00e4003082e0a8095560f2004c0d503c1c1004481da03016010100c0000b41c1d46501042410070074a10704640d04080e00c05a41d0495551004282240d1220314210041001d21b8100500c40c1020b204d114a02e00ca18205a468010b504400c80c1c21038070544012031509902003088082c1c2c2d1000d40c041c1d6200103841c3d00301c07110f101080c1441e040204d0b851041c102d8640c01c2c44008034aa500c180281d40c0380f120a074868046035203030b18036550302070a080e0448480500c03c03501d05c940800c009000b03140003000000d1510305826600c8000504500080c0c21030100d0354040d00305100c00c6903112074138a03503041c0c001e20f40191944a91442c4c20181544a40440ba240c2062600000704140000114003501d41290510407a14079001800150482d411560340d504900d000e68405c02409100d009111504c000c0084c25031090840c00ca1400da0058001560f01135034806181240d4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 762406465 1250 762405215 762405223
    0x1824010311040519091e050a121409010809031c0e19080307051e040303091d0412080c042112180504271520030c1312050a05 55
    0x4540c180e8091010740fa104e08004048800e02214403d9250b8515086003400000768590f0000744204e0024140c40800c2d040041c1d5595155209507400134102c2000040f5601609908065481c04110682401d004000545483d2402800041e00c2c1c0820811080301c8c62242128400c10519a240010101011300c400c41c0b41550310300c0c0086072019502081d8001c00c29050540f03600c8102440c15940d00d4049043e01170a03203440113000c0300b4190012801000309604034200c00150340c100e140380c14501e40515034640d500041030728060000c0251601c9000c0040c07060004661242440032294582503544029143e10070080705c0280c41c80580b1522101080415002c0145610541c64001c455036101d010034881282c2a2044600c200c0d51100c1184007040c1842c4260503047c000240c6411b10651800c00400503032a440300311072141d1404039080c2d410b0140415190000340d05030140c0703096070307680c40c0062600d80c04003500b05040c0d12056400501c00140a0101080301d2040c00680f110383c54a01d8200c5c54 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 762407715 1250 762406465 762406493
    0x12120a110d090b0a06060e0315101502073003030507030e0f1b010323040f0204050403080402041b0504030b060a050a0312090608070c08090d0204050c090a090b010818240103 76
    0x4000c4080940c24280c0c8d0001441d030003020720407402c031030540c441030034100c00c42c40d2a034000c0d801c040318824205d510a401041540850381203030000810400d90003203080402d4401c0c0d44110f03c540c60b207607980021901c2903008540c46099400c0000380c2400100c980c1d484e0400d0030b07000f0110b5900001ca0746119003407040c7c000b0a08942801c0510503001d20940c1000700ad100366010410141038440054140062441d1840119070003500402260615060003040c1e903c2c01c0728160f004500b001621501d507040c2c00f05500501440e035a035507080c030b411a96010300103070015003916800005070001260035500e0301d8004c40254400c1a890072400c0f00460003400907541540b22800707000e00e000c2003041894210f100d5540703540e0302ca12a42d55640c0f0410016040b0040110082c0d002440c25003006045a070303000061a1250f02203503680c1043d95a442d06c503041d81d0710b03007192500180d05c9401080240c440e6694440340021014240c0b5800d40c03001100c034108505a54044000e590234400400c14031100306900c10b4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 762408965 1250 762407715 762407717
    0x60902030903030414100c031a0f220f0e0703050d02060702120304150e0607020712050a03030e032106100206040209041b0b030a090512120a110d090b0a0606 69
    0x4103614100034010b840e40001040600942a20307074001c591124180f21172400203120301400c000010040c0d100a0051a82074110040040c403668922078a24019454120306a00144200a8900b902c0300002c1c07220301001e00c224009446a0084180e01d80d140640392020210000074200285141082c614109001c41c41070255000542440320762030b40407510100303030b681c0054119541d032564a0314500e01c80400d140410002d28104c1015075a410118115010358050307800c403000305459051041180040b203800400b0756008589250001c0d0190300604070702180d00d41641d060110340c00760742060180c10031074811485203190070026a8034141c543c2e03000d88100c510051100d483d065000c00c0c40080042d00203015030150424141c021205407642001074004011090780303c1c1001da10000140501c02021102c9000d99490701c0303040110001558509c0485110909660b20307034454000c0209820303860b844d0b208404002c840d00b2039426001c1d06403a54846e54400c0035629100c1102c2080340c10b0361304150 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 762410071 1106 762408965 762408967
    0x806060c0102120609070f0206160203120f0402091006050304020f0a1208040f0b0a09031b0b070f051b030d0302181c11060a09090e01090204110d060902 67
    0x4e024810030745020f001034a507454103840510f01c0d40c090000507441040001d0a0305041404910f0001c414015030f807521440d04808491001c1c120b40c0c40c0002c11884040c803046040c400b03d4258000086041d18420300c1c2056402410381c440580040d00c987c1a06280145030799900700741e040103248602c140c0210580501c0c0042040d0024440c0d980030702841c1400190200403182203032210090350b0340d2504250f0869541e1580d8641c2e41c102c101400010510126618a1801c0107140300c0307000b102807903091803982c0f512a10b405000b42500084043c2e042c000145520000307001810300e44c05050141e1103603400e0758000410785441c444164000003c1640300d941d00034620012000c0c0c1d01070708848170390001d03290074486940701e8024054000740b030b20349007040000c1440d8016000c0d0741e02130300041102541a000034069510300c01c0c1206161030009140380080a41c2d20648005000f908425 = true := by decide +kernel

theorem cover : BRFrame.Cov 762230215 762410071 := by
  have h0 := BRFrame.cov_init 762230215
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762230215 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 762230215 ≤ n) (h2 : n < 762410071) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
