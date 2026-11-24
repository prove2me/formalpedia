-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.FormalGroupLaws.funEqType_lgF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:06.163137+00:00
-- url     : https://prove2.me/submissions/56ebf7f1-83b8-4e2d-8faa-b1546f8d09dd

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_HomPsSubstMvSubst
import Definitions.Def_Formalism_TorsionNormIteration_LubinTateExample
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FrobSqV
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_CoeffSubstLgFOfDegreeOne
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_lgF_funEq

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
namespace Formalism.InvariantFactorPaths.G7.FormalGroupLaws
theorem _root_.solution (p : ℕ) [hp : Fact p.Prime] :
    Formalism.G.IsFunEqType p (p ^ 2) (RingHom.id ℚ_[p]) (lgF ℚ_[p] p) := by
  have hp2 : 2 ≤ p := hp.out.two_le
  have hpK : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  unfold Formalism.G.IsFunEqType
  simp only [PowerSeries.map_id, id]
  rw [lgF_funEq p hp2 hpK]
  intro n
  rw [PowerSeries.coeff_X]
  split_ifs <;> simp
end Formalism.InvariantFactorPaths.G7.FormalGroupLaws
