-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.invOn_empty
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:01:03.34535+00:00
-- url     : https://prove2.me/submissions/e0bbf0f1-6241-47a9-a308-7679c63d3403

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_mem_invOn

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
variable {n : ℕ}
variable {R : Type u} [CommRing R]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : invOn (∅ : Finset (Fin n)) = {1} := by
  ext σ
  rw [mem_invOn, Finset.mem_singleton]
  constructor
  · rintro ⟨_, h⟩
    exact Equiv.ext fun i => h i (Finset.notMem_empty i)
  · rintro rfl
    simp
end Formalism.DworkPowerSeriesWeights
