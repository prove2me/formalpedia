-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.chebyshev_theta_log_four
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:48.533441+00:00
-- url     : https://prove2.me/submissions/8fdfe85b-8c1b-4017-961e-2e422cf85928

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementC
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_AbsorbLocalConditions
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ErrSum
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_UnipotentNumeric
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_WeightedPlaceLogSum
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsComposeGeneral
import Theorems.Thm_Formalism_DivisionValues_WeightedPlaceLogSum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution : ThetaLog4 := by
  classical
  intro Y hY Q hQ
  refine le_trans ?_ (Chebyshev.theta_le_log4_mul_x hY)
  unfold Chebyshev.theta
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro p hp
    obtain ⟨h1, h2⟩ := hQ p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨h1.pos, Nat.le_floor h2⟩, h1⟩
  · intro p _ _
    exact Real.log_natCast_nonneg p
end Formalism.EigenvalueLevelCeiling
