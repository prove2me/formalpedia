-- Prove2me | solution 1 for BroughanRH.matiyasevichInteger
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-24T04:45:13.014809+00:00
-- url     : https://prove2.me/submissions/f6e98dc2-5880-4539-a807-6d2733cb0d1d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BroughanRH_schoenfeldPsi
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_psi_le
import Mathlib

set_option autoImplicit false
open Finset

namespace MatI

noncomputable def Aalt (n : ℕ) : ℝ := ∑ k ∈ Ico 1 n, (-1:ℝ)^(k+1) / k
noncomputable def Qf (n : ℕ) : ℝ := ∏ i ∈ Ico 1 n, ((2*i+5 : ℝ) / (2*i))
noncomputable def Ef (n : ℕ) : ℝ := ∏ i ∈ Ico 1 n, (2*i : ℝ)

lemma Ef_eq (n : ℕ) (hn : 1 ≤ n) : Ef n = ((2^(n-1) * (n-1).factorial : ℕ) : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base => simp [Ef]
  | succ n hn ih =>
    rw [Ef, Finset.prod_Ico_succ_top hn, ← Ef, ih]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    push_cast
    rw [Nat.factorial_succ]; push_cast; ring

lemma Ef_pos (n : ℕ) : 0 < Ef n := by
  apply Finset.prod_pos; intro i hi; simp at hi
  have : (1:ℝ) ≤ i := by exact_mod_cast hi.1
  linarith

lemma EQ_eq (n : ℕ) (hn : 1 ≤ n) : Ef n * Qf n = ((∏ j ∈ Icc 2 n, (2*j+3) : ℕ) : ℝ) := by
  rw [Ef, Qf, ← Finset.prod_mul_distrib]
  have h1 : ∀ i ∈ Ico 1 n, (2*i : ℝ) * ((2*i+5 : ℝ) / (2*i)) = 2*i+5 := by
    intro i hi; simp at hi
    have h1' : (1:ℝ) ≤ i := by exact_mod_cast hi.1
    have : (2*i:ℝ) ≠ 0 := by linarith
    field_simp
  rw [Finset.prod_congr rfl h1]
  push_cast
  -- reindex j = i + 1
  have : Icc 2 n = (Ico 1 n).map ⟨(· + 1), add_left_injective 1⟩ := by
    ext j; simp only [mem_Icc, mem_map, mem_Ico, Function.Embedding.coeFn_mk]
    constructor
    · intro h; exact ⟨j - 1, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩; omega
  rw [this, Finset.prod_map]
  apply Finset.prod_congr rfl; intro i _
  simp; ring

/-- The algebraic reduction. -/
lemma reduction (n : ℕ) (hn : 1 ≤ n) (π l : ℕ) :
    let evenFact (m : ℕ) := 2^m * m.factorial
    let d : ℤ := ∑ k ∈ Finset.Ico 1 n, (-1 : ℤ)^(k+1) * ((evenFact (n-1) / k : ℕ) : ℤ)
    let f₀ := evenFact n / 2
    (((π : ℤ)^2 * (d * (l : ℤ) - (f₀ : ℤ)) : ℤ) : ℝ) = (π:ℝ)^2 * Ef n * (Aalt n * l - n) := by
  intro evenFact d f₀
  have hE := Ef_eq n hn
  have hd : (d : ℝ) = Ef n * Aalt n := by
    simp only [d, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      Int.cast_natCast]
    rw [Aalt, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk; simp at hk
    have hdvd : k ∣ evenFact (n-1) := by
      simp only [evenFact]
      exact Dvd.dvd.mul_left (Nat.dvd_factorial (by omega) (by omega)) _
    have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk.1
    rw [Nat.cast_div hdvd (by linarith)]
    rw [hE]; simp only [evenFact]; push_cast; ring
  have hf : (f₀ : ℝ) = Ef n * n := by
    simp only [f₀, evenFact]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [show 2^(m+1) * (m+1).factorial = (2^m * (m+1).factorial) * 2 by ring, Nat.mul_div_cancel _ (by norm_num)]
    rw [hE]; simp only [Nat.add_sub_cancel]; push_cast
    rw [Nat.factorial_succ]; push_cast; ring
  push_cast
  rw [hd, hf]; ring


/-! ### Alternating harmonic sums -/

noncomputable def Hs (n : ℕ) : ℝ := ∑ k ∈ Icc 1 n, (1:ℝ)/k

lemma Hs_succ (n : ℕ) : Hs (n+1) = Hs n + 1/((n:ℝ)+1) := by
  rw [Hs, Finset.sum_Icc_succ_top (by omega), ← Hs]; push_cast; ring

lemma Aalt_succ (n : ℕ) (hn : 1 ≤ n) : Aalt (n+1) = Aalt n + (-1:ℝ)^(n+1) / n := by
  rw [Aalt, Finset.sum_Ico_succ_top hn, ← Aalt]

lemma Aalt_odd (j : ℕ) : Aalt (2*j+1) + Hs j = Hs (2*j) := by
  induction j with
  | zero => simp [Aalt, Hs]
  | succ j ih =>
    have e1 : (-1:ℝ)^(2*j+1+1) = 1 := by
      rw [show 2*j+1+1 = 2*(j+1) by ring, pow_mul]; norm_num
    have e2 : (-1:ℝ)^(2*j+2+1) = -1 := by
      rw [show 2*j+2+1 = 2*(j+1)+1 by ring, pow_succ, pow_mul]; norm_num
    rw [show 2*(j+1)+1 = (2*j+2)+1 by ring, Aalt_succ _ (by omega),
      show 2*j+2 = (2*j+1)+1 by ring, Aalt_succ _ (by omega), e1,
      show 2*(j+1) = (2*j+1)+1 by ring, Hs_succ, Hs_succ, Hs_succ, ← ih, e2]
    push_cast
    have h1 : (0:ℝ) < j + 1 := by positivity
    field_simp
    ring

lemma Hs_sub_le (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Hs b - Hs a ≤ Real.log b - Real.log a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [Hs_succ]
    have hb0 : (0:ℝ) < b := by have : (1:ℝ) ≤ b := by exact_mod_cast (le_trans ha hb)
                               linarith
    have key : 1/((b:ℝ)+1) ≤ Real.log ((b:ℝ)+1) - Real.log b := by
      have := Real.one_sub_inv_le_log_of_pos (x := ((b:ℝ)+1)/b) (by positivity)
      rw [Real.log_div (by positivity) hb0.ne'] at this
      convert this using 1
      field_simp; ring
    push_cast
    linarith

lemma Aalt_odd_le (j : ℕ) : Aalt (2*j+1) ≤ Real.log 2 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [Aalt]; exact (Real.log_pos (by norm_num)).le
  have h := Aalt_odd j
  have h2 := Hs_sub_le j (2*j) hj (by omega)
  have : Real.log ((2*j : ℕ):ℝ) - Real.log j = Real.log 2 := by
    push_cast
    rw [Real.log_mul (by norm_num) (by positivity)]; ring
  linarith

lemma Aalt_le (n : ℕ) (hn : 2 ≤ n) : Aalt n ≤ Real.log 2 + 1/((n:ℝ)-1) := by
  obtain ⟨j, rfl | rfl⟩ : ∃ j, n = 2*j+1 ∨ n = 2*j+2 := ⟨(n-1)/2, by omega⟩
  · have h1 := Aalt_odd_le j
    have hj : (1:ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
    have h2 : (0:ℝ) < ((2*j+1:ℕ):ℝ) - 1 := by push_cast; linarith
    have h3 : 0 < 1/(((2*j+1:ℕ):ℝ) - 1) := by positivity
    linarith
  · rw [show 2*j+2 = (2*j+1)+1 by ring, Aalt_succ _ (by omega)]
    have := Aalt_odd_le j
    have e : (-1:ℝ)^(2*j+1+1) = 1 := by
      rw [show 2*j+1+1 = 2*(j+1) by ring, pow_mul]; norm_num
    rw [e]; push_cast
    have : (2*(j:ℝ)+1+1-1) = 2*j+1 := by ring
    rw [this]; linarith

/-! ### The exponent `l` -/

lemma l_bound (n : ℕ) : (Nat.log2 ((Finset.Icc 1 n).lcm id) : ℝ) * Real.log 2 ≤ Chebyshev.psi n := by
  rw [Chebyshev.psi_eq_log_lcmUpto]
  have hne : Nat.lcmUpto n ≠ 0 := Nat.lcmUpto_ne_zero n
  have h := Nat.log2_self_le hne
  have h' : ((2:ℝ))^(Nat.log2 (Nat.lcmUpto n)) ≤ (Nat.lcmUpto n : ℝ) := by exact_mod_cast h
  have := Real.log_le_log (by positivity) h'
  rw [Real.log_pow] at this
  exact this

/-! ### Prime counting -/

lemma pi_le_third (n : ℕ) (hn : 6 ≤ n) : (Nat.primeCounting n : ℝ) ≤ n/3 + 3 := by
  have h := Nat.primeCounting_add_le (a := 6) (k := 6) (by norm_num) le_rfl (n-6)
  rw [show 6 + (n-6) = n by omega] at h
  have h6 : Nat.primeCounting 6 = 3 := by decide
  have ht : Nat.totient 6 = 2 := by decide
  rw [h6, ht] at h
  have h1 : ((n-6)/6 : ℕ) * 6 ≤ n - 6 := Nat.div_mul_le_self _ _
  have h2 : (((n-6)/6 : ℕ):ℝ) * 6 ≤ (n:ℝ) - 6 := by
    have : ((n - 6 : ℕ):ℝ) = n - 6 := by push_cast [Nat.cast_sub hn]; ring
    rw [← this]; exact_mod_cast h1
  have h3 : (Nat.primeCounting n : ℝ) ≤ 3 + 2 * ((((n-6)/6 : ℕ):ℝ) + 1) := by exact_mod_cast h
  linarith

lemma pi_le_split (n : ℕ) (y : ℝ) (hy : 1 < y) :
    (Nat.primeCounting n : ℝ) ≤ y + Chebyshev.theta n / Real.log y := by
  have hly : 0 < Real.log y := Real.log_pos hy
  rw [← Nat.primesLE_card_eq_primeCounting, Chebyshev.theta_eq_sum_primesLE_log, Finset.sum_div]
  have hpt : ∀ p ∈ Nat.primesLE n, (1:ℝ) ≤ (if (p:ℝ) ≤ y then 1 else 0) + Real.log p / Real.log y := by
    intro p hp
    have hpp := Nat.prime_of_mem_primesLE hp
    have hp1 : (1:ℝ) < p := by exact_mod_cast hpp.one_lt
    split_ifs with h
    · have : 0 ≤ Real.log p / Real.log y := div_nonneg (Real.log_nonneg hp1.le) hly.le
      linarith
    · push_neg at h
      rw [zero_add, le_div_iff₀ hly, one_mul]
      exact Real.log_le_log (by linarith) h.le
  have hs := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul, mul_one] at hs
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hs
  have hc : ((Nat.primesLE n).filter (fun p : ℕ => (p:ℝ) ≤ y)).card ≤ ⌊y⌋₊ := by
    calc _ ≤ (Finset.Icc 1 ⌊y⌋₊).card := by
          apply Finset.card_le_card
          intro p hp
          simp only [Finset.mem_filter] at hp
          have := (Nat.prime_of_mem_primesLE hp.1).one_lt
          simp only [Finset.mem_Icc]
          exact ⟨by omega, Nat.le_floor hp.2⟩
      _ = ⌊y⌋₊ := by simp
  have hc' : (((Nat.primesLE n).filter (fun p : ℕ => (p:ℝ) ≤ y)).card : ℝ) ≤ y :=
    le_trans (by exact_mod_cast hc) (Nat.floor_le (by linarith))
  linarith

/-! ### Lower bound for `Q` -/

lemma Qf_succ (n : ℕ) (hn : 1 ≤ n) : Qf (n+1) = Qf n * ((2*n+5)/(2*n)) := by
  rw [Qf, Finset.prod_Ico_succ_top hn, ← Qf]

lemma Qf_pos (n : ℕ) : 0 < Qf n := by
  apply Finset.prod_pos; intro i hi; simp at hi
  have : (1:ℝ) ≤ i := by exact_mod_cast hi.1
  apply div_pos <;> linarith

lemma Qf_74 : ((89/1000):ℝ) * 75^5 ≤ Qf 74 ^ 2 := by
  have hE := Ef_eq 74 (by norm_num)
  have hEQ := EQ_eq 74 (by norm_num)
  have hEp := Ef_pos 74
  have hQ : Qf 74 = ((∏ j ∈ Icc 2 74, (2*j+3) : ℕ) : ℝ) / Ef 74 := by
    rw [← hEQ]; field_simp
  have key : 89 * 75^5 * (2^(74-1) * (74-1).factorial)^2 ≤ 1000 * (∏ j ∈ Icc 2 74, (2*j+3))^2 := by
    decide
  rw [hQ, hE]
  rw [hE] at hEp
  generalize (∏ j ∈ Icc 2 74, (2*j+3)) = P at key ⊢
  generalize 2^(74-1) * (74-1).factorial = E at key hEp ⊢
  have : ((89 * 75^5 * E^2 : ℕ):ℝ) ≤ ((1000*P^2 : ℕ):ℝ) := by exact_mod_cast key
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at this
  rw [div_pow, le_div_iff₀ (by positivity)]
  linarith

lemma Qf_lower (n : ℕ) (hn : 74 ≤ n) : ((89/1000):ℝ) * ((n:ℝ)+1)^5 ≤ Qf n ^ 2 := by
  induction n, hn using Nat.le_induction with
  | base => have := Qf_74; norm_num at this ⊢; linarith
  | succ n hn ih =>
    rw [Qf_succ n (by omega), mul_pow]
    have hn' : (74:ℝ) ≤ n := by exact_mod_cast hn
    have hpoly : ((n:ℝ)+1)^5 * (2*n+5)^2 ≥ 4*(n:ℝ)^2*((n:ℝ)+2)^5 := by
      nlinarith [pow_pos (show (0:ℝ) < n by linarith) 5, pow_pos (show (0:ℝ) < n by linarith) 4,
        pow_pos (show (0:ℝ) < n by linarith) 3, pow_pos (show (0:ℝ) < n by linarith) 2]
    have hpos : (0:ℝ) < 2*n := by linarith
    rw [div_pow, mul_div_assoc', le_div_iff₀ (by positivity)]
    push_cast
    calc ((89/1000):ℝ) * ((n:ℝ)+1+1)^5 * (2*n)^2 = (89/1000) * (4*(n:ℝ)^2*((n:ℝ)+2)^5) := by ring
      _ ≤ (89/1000) * (((n:ℝ)+1)^5 * (2*n+5)^2) := by gcongr
      _ = ((89/1000) * ((n:ℝ)+1)^5) * (2*n+5)^2 := by ring
      _ ≤ Qf n ^ 2 * (2*n+5)^2 := by gcongr

end MatI

namespace MatI

/-! ### The bracket `A l - n` -/

lemma bracket_bound (n : ℕ) (hn : 74 ≤ n) (l : ℕ)
    (hl : (l:ℝ) * Real.log 2 ≤ Chebyshev.psi n)
    (hS : Chebyshev.psi n - n < Real.sqrt n * (Real.log n)^2 / (8 * Real.pi))
    (hψ : Chebyshev.psi n ≤ 1.04 * n) :
    Aalt n * l - n ≤ Real.sqrt n * (Real.log n)^2 / (8 * Real.pi) + 1.53 := by
  have hA := Aalt_le n (by omega)
  have hx : (74:ℝ) ≤ n := by exact_mod_cast hn
  have hl0 : (0:ℝ) ≤ l := Nat.cast_nonneg l
  have hlog2 := Real.log_two_gt_d9
  have hn1 : (0:ℝ) < (n:ℝ) - 1 := by linarith
  have hlb : (l:ℝ) * 0.6931 ≤ 1.04 * n := by nlinarith
  have hl153 : (l:ℝ) ≤ 1.53 * ((n:ℝ) - 1) := by nlinarith
  have hdiv : (l:ℝ) / ((n:ℝ) - 1) ≤ 1.53 := by rw [div_le_iff₀ hn1]; linarith
  have : Aalt n * l ≤ (Real.log 2 + 1/((n:ℝ)-1)) * l := mul_le_mul_of_nonneg_right hA hl0
  have e : (Real.log 2 + 1/((n:ℝ)-1)) * l = l * Real.log 2 + l / ((n:ℝ)-1) := by ring
  linarith

/-! ### Final numerical comparison, range `74 ≤ x ≤ e^7` -/

lemma Q_ge (x Q : ℝ) (hx : 0 ≤ x) (hQ : 0 ≤ Q) (hQ2 : (89/1000:ℝ) * (x+1)^5 ≤ Q^2) :
    0.2983 * (x+1)^2 * Real.sqrt (x+1) ≤ Q := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ x+1 by linarith)
  have hs0 := Real.sqrt_nonneg (x+1)
  have h0 : 0 ≤ 0.2983 * (x+1)^2 * Real.sqrt (x+1) := by positivity
  have hsq : (0.2983 * (x+1)^2 * Real.sqrt (x+1))^2 ≤ Q^2 := by
    have : (0.2983 * (x+1)^2 * Real.sqrt (x+1))^2 = 0.2983^2 * (x+1)^4 * (Real.sqrt (x+1))^2 := by ring
    rw [this, hs]
    have : (0:ℝ) ≤ (x+1)^5 := by positivity
    nlinarith
  exact (pow_le_pow_iff_left₀ h0 hQ (by norm_num)).1 hsq

lemma final_small (x P Q : ℝ) (hx : 74 ≤ x) (hlog : Real.log x ≤ 7) (hP0 : 0 ≤ P)
    (hP : P ≤ x/3 + 3) (hQ : 0 ≤ Q) (hQ2 : (89/1000:ℝ) * (x+1)^5 ≤ Q^2) :
    P^2 * (Real.sqrt x * (Real.log x)^2 / (8 * Real.pi) + 1.53) < Q := by
  have hQ' := Q_ge x Q (by linarith) hQ hQ2
  set s := Real.sqrt (x+1) with hsdef
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ x+1 by linarith)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs866 : 8.66 ≤ s := by nlinarith
  have hsx : Real.sqrt x ≤ s := Real.sqrt_le_sqrt (by linarith)
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hl2 : (Real.log x)^2 ≤ 49 := by nlinarith
  have hpi := Real.pi_gt_d2
  have hB : Real.sqrt x * (Real.log x)^2 / (8 * Real.pi) ≤ 1.951 * s := by
    rw [div_le_iff₀ (by positivity)]
    have : Real.sqrt x * (Real.log x)^2 ≤ s * 49 :=
      mul_le_mul hsx hl2 (sq_nonneg _) hs0
    nlinarith [mul_le_mul_of_nonneg_left hpi.le hs0]
  have hPx : P ≤ 0.369 * (x+1) := by linarith
  have hP2 : P^2 ≤ 0.136161 * (x+1)^2 := by nlinarith
  have hBpos : 0 ≤ Real.sqrt x * (Real.log x)^2 / (8 * Real.pi) + 1.53 := by positivity
  calc P^2 * (Real.sqrt x * (Real.log x)^2 / (8 * Real.pi) + 1.53)
      ≤ 0.136161 * (x+1)^2 * (1.951 * s + 1.53) := by
        apply mul_le_mul hP2 (by linarith) hBpos (by positivity)
    _ < 0.2983 * (x+1)^2 * s := by
        have : (0:ℝ) < (x+1)^2 := by positivity
        nlinarith
    _ ≤ Q := hQ'

/-! ### Range `x > e^7` -/

lemma exp_seven_fourths : (5.74:ℝ) ≤ Real.exp (7/4) := by
  have he := Real.exp_one_gt_d9
  have h7 : Real.exp (7/4) ^ 4 = Real.exp 1 ^ 7 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
  have h1 : (5.74:ℝ)^4 ≤ Real.exp (7/4) ^ 4 := by
    rw [h7]
    have : (2.7182818283:ℝ)^7 ≤ Real.exp 1 ^ 7 := pow_le_pow_left₀ (by norm_num) he.le 7
    nlinarith
  exact (pow_le_pow_iff_left₀ (by norm_num) (Real.exp_pos _).le (by norm_num)).1 h1

lemma final_large (u e P Q B : ℝ) (hu : 7 ≤ u) (he : e = Real.exp (u/4))
    (hP0 : 0 ≤ P) (hP : P ≤ e^3 + 1.04 * e^4 / (3 * (u/4)))
    (hB : B = e^2 * u^2 / (8 * Real.pi) + 1.53)
    (hQ : 0.2983 * e^10 ≤ Q) : P^2 * B < Q := by
  have h74 := exp_seven_fourths
  have hepos : 0 < e := by rw [he]; exact Real.exp_pos _
  -- e ≥ u * (5.74/7)
  have hue : u * (5.74/7) ≤ e := by
    have h1 : Real.exp (u/4) = Real.exp (7/4) * Real.exp ((u-7)/4) := by
      rw [← Real.exp_add]; ring_nf
    have h2 := Real.add_one_le_exp ((u-7)/4)
    have h3 : 0 ≤ (u-7)/4 + 1 := by linarith
    rw [he, h1]
    calc u * (5.74/7) ≤ 5.74 * ((u-7)/4 + 1) := by nlinarith
      _ ≤ Real.exp (7/4) * ((u-7)/4 + 1) := by gcongr
      _ ≤ _ := by gcongr
  have he574 : 5.74 ≤ e := by
    rw [he]; exact le_trans h74 (Real.exp_le_exp.2 (by linarith))
  have hu0 : 0 < u := by linarith
  have hPu : P * u ≤ 2.6062 * e^4 := by
    have : P * u ≤ e^3 * u + (1.04 * 4 / 3) * e^4 := by
      have := mul_le_mul_of_nonneg_right hP hu0.le
      have e1 : (e^3 + 1.04 * e^4 / (3 * (u/4))) * u = e^3 * u + (1.04*4/3) * e^4 := by
        field_simp
      linarith
    have : e^3 * u ≤ e^3 * (e * (7/5.74)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
    nlinarith [pow_pos hepos 4]
  have hP7 : P * 7 ≤ 2.6062 * e^4 := le_trans (mul_le_mul_of_nonneg_left hu hP0) hPu
  have hpi := Real.pi_gt_d2
  have hpi0 : 0 < 8 * Real.pi := by positivity
  have hT1 : P^2 * (e^2 * u^2 / (8 * Real.pi)) ≤ 0.2705 * e^10 := by
    rw [show P^2 * (e^2 * u^2 / (8 * Real.pi)) = (P*u)^2 * e^2 / (8 * Real.pi) by ring,
      div_le_iff₀ hpi0]
    have hPu0 : 0 ≤ P * u := by positivity
    have : (P*u)^2 ≤ (2.6062 * e^4)^2 := pow_le_pow_left₀ hPu0 hPu 2
    have : (P*u)^2 * e^2 ≤ (2.6062 * e^4)^2 * e^2 := mul_le_mul_of_nonneg_right this (by positivity)
    have e1 : (2.6062 * e^4)^2 * e^2 = 6.79227844 * e^10 := by ring
    nlinarith [mul_le_mul_of_nonneg_left hpi.le (pow_pos hepos 10).le]
  have hT2 : P^2 * 1.53 ≤ 0.2121 * e^8 := by
    have : (P*7)^2 ≤ (2.6062 * e^4)^2 := pow_le_pow_left₀ (by positivity) hP7 2
    nlinarith [pow_pos hepos 8]
  have he2 : 32 ≤ e^2 := by nlinarith
  have : 0.2121 * e^8 < (0.2983 - 0.2705) * e^10 := by
    have : e^10 = e^8 * e^2 := by ring
    rw [this]; nlinarith [pow_pos hepos 8]
  rw [hB, mul_add]
  linarith

end MatI

namespace MatI

lemma core (n : ℕ) (hn : 74 ≤ n) :
    (Nat.primeCounting n : ℝ)^2 * (Aalt n * (Nat.log2 ((Finset.Icc 1 n).lcm id) : ℝ) - n) < Qf n := by
  set l := Nat.log2 ((Finset.Icc 1 n).lcm id)
  set P : ℝ := ((Nat.primeCounting n : ℕ) : ℝ) with hPdef
  have hx : (74:ℝ) ≤ n := by exact_mod_cast hn
  have hS0 := BroughanRH.schoenfeldPsi n (by linarith)
  have hS : Chebyshev.psi n - n < Real.sqrt n * (Real.log n)^2 / (8 * Real.pi) :=
    lt_of_le_of_lt (le_abs_self _) hS0
  have hψ := TaoFivePrimes.rosser_schoenfeld_psi_le n (by linarith)
  have hbr := bracket_bound n hn l (l_bound n) hS hψ
  have hQ0 := Qf_pos n
  have hQ2 := Qf_lower n hn
  have hP0 : 0 ≤ P := Nat.cast_nonneg _
  have hPB : P^2 * (Real.sqrt n * (Real.log n)^2 / (8 * Real.pi) + 1.53) < Qf n := by
    by_cases h7 : Real.log n ≤ 7
    · exact final_small n P (Qf n) hx h7 hP0 (pi_le_third n (by omega)) hQ0.le hQ2
    · push Not at h7
      set u := Real.log n with hu
      set e := Real.exp (u/4) with he
      have hxe : (n:ℝ) = e^4 := by
        rw [he, ← Real.exp_nat_mul]; push_cast
        rw [show (4:ℝ)*(u/4) = u by ring, hu, Real.exp_log (by linarith)]
      have he1 : 1 < e^3 := one_lt_pow₀ (by rw [he]; exact Real.one_lt_exp_iff.2 (by linarith)) (by norm_num)
      have hlogy : Real.log (e^3) = 3 * (u/4) := by
        rw [Real.log_pow, he, Real.log_exp]; push_cast; ring
      have hπ := pi_le_split n (e^3) he1
      rw [hlogy] at hπ
      have hθ : Chebyshev.theta n ≤ 1.04 * e^4 := by
        rw [← hxe]; exact le_trans (Chebyshev.theta_le_psi _) hψ
      have hP : P ≤ e^3 + 1.04 * e^4 / (3*(u/4)) := by
        have : Chebyshev.theta n / (3*(u/4)) ≤ 1.04 * e^4 / (3*(u/4)) :=
          div_le_div_of_nonneg_right hθ (by linarith)
        linarith
      have he0 : 0 < e := Real.exp_pos _
      have hsq : Real.sqrt n = e^2 := by
        rw [hxe, show e^4 = (e^2)^2 by ring, Real.sqrt_sq (by positivity)]
      have hQ := Q_ge n (Qf n) (by linarith) hQ0.le hQ2
      have hQ' : 0.2983 * e^10 ≤ Qf n := by
        refine le_trans ?_ hQ
        have h10 : e^10 = (n:ℝ)^2 * Real.sqrt n := by rw [hsq, hxe]; ring
        rw [h10]
        have h1 : (n:ℝ)^2 ≤ ((n:ℝ)+1)^2 := by nlinarith
        have h2 : Real.sqrt n ≤ Real.sqrt ((n:ℝ)+1) := Real.sqrt_le_sqrt (by linarith)
        have := mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by positivity)
        nlinarith
      exact final_large u e P (Qf n) _ (by linarith) rfl hP0 hP (by rw [hsq]) hQ'
  by_cases hneg : Aalt n * l - n ≤ 0
  · have : P^2 * (Aalt n * l - n) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
    linarith
  · calc P^2 * (Aalt n * l - n) ≤ P^2 * (Real.sqrt n * (Real.log n)^2 / (8 * Real.pi) + 1.53) :=
          mul_le_mul_of_nonneg_left hbr (by positivity)
      _ < Qf n := hPB

end MatI

set_option maxRecDepth 100000 in
theorem matiyasevich_small : let evenFact (m : ℕ) := 2^m * m.factorial
    let d (n : ℕ) : ℤ := ∑ k ∈ Finset.Ico 1 n,
      (-1 : ℤ)^(k+1) * ((evenFact (n-1) / k : ℕ) : ℤ)
    let l (n : ℕ) := Nat.log2 ((Finset.Icc 1 n).lcm id)
    let f₀ (n : ℕ) := evenFact n / 2
    let f₃ (n : ℕ) : ℕ := ∏ j ∈ Finset.Icc 2 n, (2*j+3)
    ∀ n < 74, 1 ≤ n → (Nat.primeCounting n : ℤ)^2 *
      (d n * (l n : ℤ) - (f₀ n : ℤ)) < (f₃ n : ℤ) := by decide

theorem solution :
    let evenFact (m : ℕ) := 2^m * m.factorial
    let d (n : ℕ) : ℤ := ∑ k ∈ Finset.Ico 1 n,
      (-1 : ℤ)^(k+1) * ((evenFact (n-1) / k : ℕ) : ℤ)
    let l (n : ℕ) := Nat.log2 ((Finset.Icc 1 n).lcm id)
    let f₀ (n : ℕ) := evenFact n / 2
    let f₃ (n : ℕ) : ℕ := ∏ j ∈ Finset.Icc 2 n, (2*j+3)
    ∀ n : ℕ, 1 ≤ n → (Nat.primeCounting n : ℤ)^2 *
      (d n * (l n : ℤ) - (f₀ n : ℤ)) < (f₃ n : ℤ) := by
  intro evenFact d l f₀ f₃ n hn
  by_cases hs : n < 74
  · exact matiyasevich_small n hs hn
  push Not at hs
  have hred := MatI.reduction n hn (Nat.primeCounting n) (l n)
  have hEQ := MatI.EQ_eq n hn
  have hcore := MatI.core n hs
  have hE := MatI.Ef_pos n
  simp only at hred
  simp only [d, f₀, f₃, l, evenFact] at *
  have key : (((Nat.primeCounting n : ℤ)^2 * ((∑ k ∈ Finset.Ico 1 n,
      (-1 : ℤ)^(k+1) * ((2^(n-1) * (n-1).factorial / k : ℕ) : ℤ)) *
      (Nat.log2 ((Finset.Icc 1 n).lcm id) : ℤ) - ((2^n * n.factorial / 2 : ℕ) : ℤ)) : ℤ) : ℝ)
      < (((∏ j ∈ Finset.Icc 2 n, (2*j+3) : ℕ) : ℤ) : ℝ) := by
    rw [hred, Int.cast_natCast, ← hEQ]
    have := mul_lt_mul_of_pos_left hcore hE
    nlinarith
  exact_mod_cast key

