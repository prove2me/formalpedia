-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.dirD_quadSer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:32.731808+00:00
-- url     : https://prove2.me/submissions/f2b4a37c-5e3e-47b7-b1ba-6b6e3cb8ed1f

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_dirD_X
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_dirD_C

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
universe u
open Formalism Formalism.DworkPowerSeriesWeights
variable {K : Type u} [Field K] {ι : Type} [Fintype ι]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (c : ι → ι → K) (L : ι → K) : dirD L (quadSer c) = linSer c L := by
  unfold quadSer linSer
  rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Derivation.leibniz, dirD_X, dirD_C, smul_eq_mul]
  ring
end Formalism.DworkPowerSeriesWeights
