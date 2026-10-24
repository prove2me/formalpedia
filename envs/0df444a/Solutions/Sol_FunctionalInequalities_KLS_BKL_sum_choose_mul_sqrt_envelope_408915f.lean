-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.sum_choose_mul_sqrt_envelope_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:18:33.483267+00:00
-- url     : https://prove2.me/submissions/db733256-87fa-4c01-8b77-97b59c85337e

import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_CumulantEnvelope
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Choose.Basic
import Theorems.Thm_FunctionalInequalities_KLS_BKL_choose_mul_sqrt_envelope_408915f

noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.BKL
end FunctionalInequalities.KLS.BKL
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.BKL
namespace FunctionalInequalities.KLS.BKL
end FunctionalInequalities.KLS.BKL
open FunctionalInequalities.KLS.BKL in
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
      exact FunctionalInequalities.KLS.BKL.choose_mul_sqrt_envelope_408915f hK (by omega) (by omega)

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
