-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.sum_choose_mul_sqrt_envelope_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:34:45.196098+00:00
-- url     : https://prove2.me/submissions/ca50cfff-4ff5-49a2-8a7e-5f79a2bade0b

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnvelope
import Theorems.Thm_FunctionalInequalities_KLS_BKL_choose_mul_sqrt_envelope_readable

noncomputable section
/-- **BKL (106)**: the `m - 3` summands `2 ≤ a ≤ m - 2` of (104) each equal `√b_m`, so their sum is
`(m - 3) √b_m` (empty for `m = 3`). -/
theorem solution {K : ℝ} (hK : 0 ≤ K) {m : ℕ} (hm : 3 ≤ m) :
    ∑ a ∈ Finset.Icc 2 (m - 2),
        ((m - 1).choose (a - 1) : ℝ) * Real.sqrt (FunctionalInequalities.KLS.BKL.envelope K a * FunctionalInequalities.KLS.BKL.envelope K (m - a + 1)) =
      ((m - 3 : ℕ) : ℝ) * Real.sqrt (FunctionalInequalities.KLS.BKL.envelope K m) := by
    have hsum :
        ∑ a ∈ Finset.Icc 2 (m - 2),
            ((m - 1).choose (a - 1) : ℝ) *
              Real.sqrt (FunctionalInequalities.KLS.BKL.envelope K a * FunctionalInequalities.KLS.BKL.envelope K (m - a + 1)) =
          ∑ _a ∈ Finset.Icc 2 (m - 2), Real.sqrt (FunctionalInequalities.KLS.BKL.envelope K m) := by
      apply Finset.sum_congr rfl
      intro a ha
      have ha' := Finset.mem_Icc.mp ha
      exact FunctionalInequalities.KLS.BKL.choose_mul_sqrt_envelope_readable hK (by omega) (by omega)

    have hcard : (Finset.Icc 2 (m - 2)).card = m - 3 := by
      rw [Nat.card_Icc]
      omega

    calc
      ∑ a ∈ Finset.Icc 2 (m - 2),
          ((m - 1).choose (a - 1) : ℝ) *
            Real.sqrt (FunctionalInequalities.KLS.BKL.envelope K a * FunctionalInequalities.KLS.BKL.envelope K (m - a + 1)) =
          ∑ _a ∈ Finset.Icc 2 (m - 2), Real.sqrt (FunctionalInequalities.KLS.BKL.envelope K m) := hsum
      _ = (Finset.Icc 2 (m - 2)).card • Real.sqrt (FunctionalInequalities.KLS.BKL.envelope K m) := by
        rw [Finset.sum_const]
      _ = ((m - 3 : ℕ) : ℝ) * Real.sqrt (FunctionalInequalities.KLS.BKL.envelope K m) := by
        rw [hcard]
        simp [nsmul_eq_mul]
