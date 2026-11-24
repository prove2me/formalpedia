-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.matching_existence
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:38:00.49854+00:00
-- url     : https://prove2.me/submissions/ddaf41dd-062d-41d7-b8ca-49eaaa70f861

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_mem_invOn
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_matchings_on
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qi22_homW_prod__0e07eaea3260
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46


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
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : Matchings.{u} := by
  intro K _ _ ι _ c S sg n L
  rw [matchings_on c S L Finset.univ sg]
  have hset : invOn (Finset.univ : Finset (Fin n)) =
      Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ * σ = 1) := by
    ext σ
    simp [mem_invOn]
  rw [hset]
  rfl
end Formalism.DworkPowerSeriesWeights
