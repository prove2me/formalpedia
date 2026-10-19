-- Prove2me | solution 1 for BookProof.WeakSecondDeriv.absolutelyContinuous_test
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-19T05:45:51.341523+00:00
-- url     : https://prove2.me/submissions/1c5843b4-049e-4292-a523-99705e5c15e3

-- Generated from ChapterWeakSecondDerivative.lean — solution of BookProof.WeakSecondDeriv.absolutelyContinuous_test
import Mathlib
import Definitions.Def_ChapterWeakSecondDerivative
import Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_hasCompactSupport
import Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_continuous
import Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_differentiable
import Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_deriv
open BookProof.WeakSecondDeriv




open MeasureTheory Filter Topology intervalIntegral Set

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in

theorem solution {g : ℝ → ℝ} (hg : IsTestFun g) (a b : ℝ) :
    AbsolutelyContinuousOnInterval g a b := by
  obtain ⟨x₀, hx₀⟩ := hg.deriv.continuous.norm.exists_forall_ge_of_hasCompactSupport
    hg.deriv.hasCompactSupport.norm
  refine (LipschitzWith.lipschitzOnWith (K := ⟨‖deriv g x₀‖, norm_nonneg _⟩)
    (lipschitzWith_of_nnnorm_deriv_le hg.differentiable fun x => ?_)).absolutelyContinuousOnInterval
  exact_mod_cast hx₀ x
