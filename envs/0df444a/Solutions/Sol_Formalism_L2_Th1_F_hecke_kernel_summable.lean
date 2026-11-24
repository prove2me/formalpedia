-- Prove2me | solution 1 for Formalism.L2.Th1.F.hecke_kernel_summable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:09:34.354094+00:00
-- url     : https://prove2.me/submissions/e7b57817-1fad-4dd8-84d0-c5980e231c96

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelIntegralValue
import Theorems.Thm_Formalism_L2_Th1_F_Hk1_norm_hk_le
import Theorems.Thm_Formalism_L2_Th1_F_Hk1_summable_norm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
namespace Formalism.L2.Th1.F
theorem _root_.solution : HkSummable := by
  intro τ s hτ hs
  exact Summable.of_norm_bounded (Hk1.summable_norm τ s hτ hs) (fun p => Hk1.norm_hk_le s _)
end Formalism.L2.Th1.F
