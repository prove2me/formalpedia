-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.swap_two_single_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:27.09481+00:00
-- url     : https://prove2.me/submissions/ec5e6596-db24-46c2-9cf8-8bf25a7c64e9

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ScalingSwapLemmas
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_sw_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_sw_one
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_coeff_swap2
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_product_single_variables


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas
open MvPowerSeries
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas
theorem _root_.solution (f g : PowerSeries K) :
    swap2 (at1 0 f * at1 1 g) = at1 0 g * at1 1 f := by
  ext n
  rw [coeff_swap2, coeff_product_single_variables (by decide) (by decide), coeff_product_single_variables (by decide)
    (by decide), sw_zero, sw_one, mul_comm]
end Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas
