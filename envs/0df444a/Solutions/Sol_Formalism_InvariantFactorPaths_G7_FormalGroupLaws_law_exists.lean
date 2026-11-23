-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.FormalGroupLaws.law_exists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:02:30.57487+00:00
-- url     : https://prove2.me/submissions/5da478a6-fc62-489a-9d1d-e5ddbc13a5b2

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_HomPsSubstMvSubst
import Definitions.Def_Formalism_TorsionNormIteration_LubinTateExample
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FrobSqV
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_CoeffSubstLgFOfDegreeOne
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_constantCoeff_lgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_coeff_one_lgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_cob_eq_zero_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_constantCoeff_inVar
import Theorems.Thm_Formalism_LT_SolveExists_proof
import Theorems.Thm_Formalism_LT_SolveP_SolveExists_proof


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
open Formalism.InvariantFactorPaths.G7.FormalGroupLaws
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.FormalGroupLaws
theorem _root_.solution (p : ℕ) (hp : 2 ≤ p) :
    ∃ F : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff F = 0 ∧ cob F (lgF K p) = 0 := by
  have h0 : MvPowerSeries.constantCoeff (at1 (0 : Fin 2) (lgF K p) + at1 1 (lgF K p)) = 0 := by
    rw [map_add, constantCoeff_inVar _ _ (constantCoeff_lgF p hp),
      constantCoeff_inVar _ _ (constantCoeff_lgF p hp), add_zero]
  obtain ⟨F, hF0, hF⟩ := Formalism.LT.SolveExists_proof K (Fin 2) (lgF K p) _
    (constantCoeff_lgF p hp) (coeff_one_lgF p hp) h0
  exact ⟨F, hF0, (cob_eq_zero_iff F _).mpr hF⟩
end Formalism.InvariantFactorPaths.G7.FormalGroupLaws
