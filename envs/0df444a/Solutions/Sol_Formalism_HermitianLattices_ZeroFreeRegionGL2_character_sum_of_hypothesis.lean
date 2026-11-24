-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.character_sum_of_hypothesis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:14.645597+00:00
-- url     : https://prove2.me/submissions/d6d6b6cf-c650-469a-9930-7648ba749820

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_WeightedVonMangoldtSumIdentity
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_weighted_sum_lipschitz
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_weight_one_sum_lipschitz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
theorem _root_.solution : CharacterSumLipschitzOfChebyshev := by
  intro hpsi
  refine ⟨fun q _ χ a w w' ha hw hww => ?_, fun a w w' ha hw hww => ?_⟩
  · refine (weighted_sum_lipschitz q χ a w w' ha hw hww).trans ?_
    have h1 := hpsi (a / w) (by positivity)
    have h2 : 0 ≤ a / w := by positivity
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    rw [mul_div_assoc]; linarith
  · refine (weight_one_sum_lipschitz a w w' ha hw hww).trans ?_
    have h1 := hpsi (a / w) (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    rw [mul_div_assoc]; linarith
end Formalism.HermitianLattices.ZeroFreeRegionGL2
