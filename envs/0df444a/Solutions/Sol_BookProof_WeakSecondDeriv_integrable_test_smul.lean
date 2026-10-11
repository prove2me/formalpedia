-- Prove2me | solution 1 for BookProof.WeakSecondDeriv.integrable_test_smul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:29:50.678742+00:00
-- url     : https://prove2.me/submissions/feda4924-eb1d-4e6f-b4d2-0134153a12b1

-- Generated from ChapterWeakSecondDerivative.lean — solution of BookProof.WeakSecondDeriv.integrable_test_smul
import Mathlib
import Definitions.Def_ChapterWeakSecondDerivative
import Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_hasCompactSupport
import Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_continuous
open BookProof.WeakSecondDeriv




open MeasureTheory Filter Topology intervalIntegral Set

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution {φ : ℝ → ℝ} (hφ : IsTestFun φ) {r : ℝ → F}
    (hr : LocallyIntegrable r volume) : Integrable (fun x => φ x • r x) volume := by

  refine (integrableOn_iff_integrable_of_support_subset (s := tsupport φ) ?_).1 ?_
  · intro x hx
    simp only [Function.mem_support] at hx
    exact subset_tsupport φ (fun h => hx (by simp [h]))
  · exact (hr.integrableOn_isCompact hφ.hasCompactSupport.isCompact).continuousOn_smul
      hφ.continuous.continuousOn hφ.hasCompactSupport.isCompact
