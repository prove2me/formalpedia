-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.absorption_le_envelope_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:32:35.041+00:00
-- url     : https://prove2.me/submissions/60071391-32c1-4085-b134-5b7ac978416b

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnvelope

noncomputable section
theorem FunctionalInequalities.KLS.BKL.envelope_nonneg {K : ℝ} (hK : 0 ≤ K) (m : ℕ) : 0 ≤ envelope K m := by
  unfold envelope
  positivity
/-- **The envelope recurrence** used to close the induction: `b_m = K (m-1)² b_{m-1}` for `m ≥ 2`. -/
theorem FunctionalInequalities.KLS.BKL.envelope_succ (K : ℝ) {m : ℕ} (hm : 2 ≤ m) :
    envelope K m = K * ((m - 1 : ℕ) : ℝ) ^ 2 * envelope K (m - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  simp only [envelope, show k + 2 - 1 = k + 1 by omega,
    Nat.factorial_succ, pow_succ]
  push_cast
  ring
/-- **Scalar absorption in the final estimate** (BKL p. 27, after (106)): for `m ≥ 3`,
`2 C m² b_{m-1} + 4 (m-3) √(b_{m-1} b_m) ≤ b_m` once `K ≥ 9C` and `K ≥ 64`. Stated for `C ≥ 0`
(the source takes `C ≥ 1`, `K ≥ max{5, 9C, 64}`). This is the arithmetic step only; it does not
close the induction (95) by itself. -/
theorem solution {K C : ℝ} (hC : 0 ≤ C) (hK9 : 9 * C ≤ K) (hK64 : 64 ≤ K)
    {m : ℕ} (hm : 3 ≤ m) :
    2 * C * (m : ℝ) ^ 2 * FunctionalInequalities.KLS.BKL.envelope K (m - 1) +
        4 * ((m - 3 : ℕ) : ℝ) * Real.sqrt (FunctionalInequalities.KLS.BKL.envelope K (m - 1) * FunctionalInequalities.KLS.BKL.envelope K m) ≤
      FunctionalInequalities.KLS.BKL.envelope K m := by
    have hKnon : 0 ≤ K := by
      linarith
    have hm2 : 2 ≤ m := by
      omega
    have hm1 : 1 ≤ m := by
      omega
    have hm3 : 3 ≤ m := hm
    have hb : 0 ≤ FunctionalInequalities.KLS.BKL.envelope K (m - 1) := by
      exact FunctionalInequalities.KLS.BKL.envelope_nonneg (K := K) hKnon (m - 1)
    have hrec := FunctionalInequalities.KLS.BKL.envelope_succ K hm2
    have hcast1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub hm1]
      norm_num
    have hcast3 : ((m - 3 : ℕ) : ℝ) = (m : ℝ) - 3 := by
      rw [Nat.cast_sub hm3]
      norm_num
    have hr : 0 ≤ (m : ℝ) - 1 := by
      rw [← hcast1]
      exact_mod_cast (Nat.zero_le (m - 1))
    have ht : 0 ≤ (m : ℝ) - 3 := by
      rw [← hcast3]
      exact_mod_cast (Nat.zero_le (m - 3))
    have hpoly : 4 * (m : ℝ) ^ 2 ≤ 9 * ((m : ℝ) - 1) ^ 2 := by
      have hfive : 0 ≤ 5 * (m : ℝ) - 3 := by
        nlinarith
      have hp : 0 ≤ ((m : ℝ) - 3) * (5 * (m : ℝ) - 3) :=
        mul_nonneg ht hfive
      nlinarith
    have hA : 4 * C * (m : ℝ) ^ 2 ≤ K * ((m : ℝ) - 1) ^ 2 := by
      have h1 := mul_le_mul_of_nonneg_left hpoly hC
      have h2 := mul_le_mul_of_nonneg_right hK9
        (sq_nonneg ((m : ℝ) - 1))
      nlinarith
    have hsK0 : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
    have hsKsq : (Real.sqrt K) ^ 2 = K := by
      simpa using Real.sq_sqrt hKnon
    have hsK : 8 ≤ Real.sqrt K := by
      nlinarith
    have hB : 8 * ((m : ℝ) - 3) ≤ Real.sqrt K * ((m : ℝ) - 1) := by
      have h1 : 8 * ((m : ℝ) - 3) ≤ 8 * ((m : ℝ) - 1) := by
        nlinarith
      have h2 : 8 * ((m : ℝ) - 1) ≤ Real.sqrt K * ((m : ℝ) - 1) :=
        mul_le_mul_of_nonneg_right hsK hr
      linarith
    have hmul :=
      mul_le_mul_of_nonneg_right hB
        (mul_nonneg hsK0 hr)
    have hcore :
        2 * C * (m : ℝ) ^ 2 +
            4 * ((m : ℝ) - 3) * Real.sqrt K * ((m : ℝ) - 1) ≤
          K * ((m : ℝ) - 1) ^ 2 := by
      nlinarith [hA, hmul, hsKsq]
    have hsq : 0 ≤ ((m : ℝ) - 1) ^ 2 :=
      sq_nonneg ((m : ℝ) - 1)
    have hKsq : 0 ≤ K * ((m : ℝ) - 1) ^ 2 :=
      mul_nonneg hKnon hsq
    have hx' :
        0 ≤ FunctionalInequalities.KLS.BKL.envelope K (m - 1) *
          (K * ((m : ℝ) - 1) ^ 2 * FunctionalInequalities.KLS.BKL.envelope K (m - 1)) := by
      exact mul_nonneg hb (mul_nonneg hKsq hb)
    have hs :
        Real.sqrt (FunctionalInequalities.KLS.BKL.envelope K (m - 1) * FunctionalInequalities.KLS.BKL.envelope K m) ^ 2 =
          FunctionalInequalities.KLS.BKL.envelope K (m - 1) *
            (K * ((m : ℝ) - 1) ^ 2 * FunctionalInequalities.KLS.BKL.envelope K (m - 1)) := by
      calc
        Real.sqrt (FunctionalInequalities.KLS.BKL.envelope K (m - 1) * FunctionalInequalities.KLS.BKL.envelope K m) ^ 2 =
            Real.sqrt
              (FunctionalInequalities.KLS.BKL.envelope K (m - 1) *
                (K * ((m : ℝ) - 1) ^ 2 * FunctionalInequalities.KLS.BKL.envelope K (m - 1))) ^ 2 := by
              rw [hrec, hcast1]
        _ = FunctionalInequalities.KLS.BKL.envelope K (m - 1) *
            (K * ((m : ℝ) - 1) ^ 2 * FunctionalInequalities.KLS.BKL.envelope K (m - 1)) :=
          Real.sq_sqrt hx'
    have hq : 0 ≤ Real.sqrt K * ((m : ℝ) - 1) * FunctionalInequalities.KLS.BKL.envelope K (m - 1) :=
      mul_nonneg (mul_nonneg hsK0 hr) hb
    have hq_sq :
        (Real.sqrt K * ((m : ℝ) - 1) * FunctionalInequalities.KLS.BKL.envelope K (m - 1)) ^ 2 =
          FunctionalInequalities.KLS.BKL.envelope K (m - 1) *
            (K * ((m : ℝ) - 1) ^ 2 * FunctionalInequalities.KLS.BKL.envelope K (m - 1)) := by
      calc
        (Real.sqrt K * ((m : ℝ) - 1) * FunctionalInequalities.KLS.BKL.envelope K (m - 1)) ^ 2 =
            (Real.sqrt K) ^ 2 * ((m : ℝ) - 1) ^ 2 *
              FunctionalInequalities.KLS.BKL.envelope K (m - 1) ^ 2 := by ring
        _ = FunctionalInequalities.KLS.BKL.envelope K (m - 1) *
            (K * ((m : ℝ) - 1) ^ 2 * FunctionalInequalities.KLS.BKL.envelope K (m - 1)) := by
          rw [hsKsq]
          ring
    have hroot :
        Real.sqrt (FunctionalInequalities.KLS.BKL.envelope K (m - 1) * FunctionalInequalities.KLS.BKL.envelope K m) =
          Real.sqrt K * ((m : ℝ) - 1) * FunctionalInequalities.KLS.BKL.envelope K (m - 1) := by
      nlinarith [hs, hq_sq,
        Real.sqrt_nonneg (FunctionalInequalities.KLS.BKL.envelope K (m - 1) * FunctionalInequalities.KLS.BKL.envelope K m)]
    have hfinal := mul_le_mul_of_nonneg_right hcore hb
    calc
      2 * C * (m : ℝ) ^ 2 * FunctionalInequalities.KLS.BKL.envelope K (m - 1) +
            4 * ((m - 3 : ℕ) : ℝ) *
              Real.sqrt (FunctionalInequalities.KLS.BKL.envelope K (m - 1) * FunctionalInequalities.KLS.BKL.envelope K m) =
          (2 * C * (m : ℝ) ^ 2 +
            4 * ((m : ℝ) - 3) * Real.sqrt K * ((m : ℝ) - 1)) *
              FunctionalInequalities.KLS.BKL.envelope K (m - 1) := by
            rw [hroot, hcast3]
            ring
      _ ≤ K * ((m : ℝ) - 1) ^ 2 * FunctionalInequalities.KLS.BKL.envelope K (m - 1) := hfinal
      _ = FunctionalInequalities.KLS.BKL.envelope K m := by
        rw [hrec, hcast1]
