-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences.swap_two_g_series
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:59:10.824415+00:00
-- url     : https://prove2.me/submissions/577608f2-5faa-466b-8352-b4e10e67cd4b

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_ThmSUniform
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FrobeniusPartialCoboundaryBound
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoefficientSupportCongruences_swap_two_a_series
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_PhiH_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_neg
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_frob_congr
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemTwo_coeff_swap2
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_coeff_swap2


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
open DworkIntegrality (Bd bd_add bd_sub bd_neg bd_mul bd_C int_mul int_pow frob_congr PhiH PhiH_apply)
open Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences
open FrobeniusSubstitution
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences
theorem _root_.solution (p : ℕ) (c c' : K) : swap2 (Gser p c c') = Gser p (-c') (-c) := by
  have hA : swap2 (AA K p 0 1) = AA K p 1 0 := swap_two_a_series p 0 1 (by simp) (by simp)
  have hB : swap2 (AA K p 1 0) = AA K p 0 1 := swap_two_a_series p 1 0 (by simp) (by simp)
  have eA : Aser K p = AA K p 0 1 := rfl
  have eB : Aser' K p = AA K p 1 0 := rfl
  ext n
  rw [Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.coeff_swap2]
  simp only [Gser, eA, eB, map_sub, MvPowerSeries.coeff_C_mul]
  rw [← Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.coeff_swap2, ← Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.coeff_swap2, hA, hB]
  ring
end Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences
