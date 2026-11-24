-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences.suppOK_Gser
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:44:10.76619+00:00
-- url     : https://prove2.me/submissions/18e54e67-11e6-48bd-9870-6b1a44769561

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_ThmSUniform
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FrobeniusPartialCoboundaryBound
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoefficientSupportCongruences_support_ok_a_zero_one
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoefficientSupportCongruences_support_ok_a_one_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_PhiH_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_neg
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_frob_congr
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open DworkIntegrality (Bd bd_add bd_sub bd_neg bd_mul bd_C int_mul int_pow frob_congr PhiH PhiH_apply)
namespace CoefficientSupportCongruences
open FrobeniusSubstitution
section Supp
variable {K : Type} [Field K]
private theorem suppOK_C_mul_sub_C_mul {p : ℕ} {G H : MvPowerSeries (Fin 2) K} (hG : SuppOK p G)
    (hH : SuppOK p H) (a b : K) :
    SuppOK p (MvPowerSeries.C a * G - MvPowerSeries.C b * H) := by
  intro n hn
  by_cases h1 : MvPowerSeries.coeff n G = 0
  · by_cases h2 : MvPowerSeries.coeff n H = 0
    · exact absurd (by simp [h1, h2]) hn
    · exact hH n h2
  · exact hG n h1
end Supp
end CoefficientSupportCongruences
end Formalism.InvariantFactorPaths.G7
end
end

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
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) (c c' : K) : SuppOK p (Gser p c c') := by
  exact suppOK_C_mul_sub_C_mul (support_ok_a_zero_one hp) (support_ok_a_one_zero hp) c c'
end Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences
