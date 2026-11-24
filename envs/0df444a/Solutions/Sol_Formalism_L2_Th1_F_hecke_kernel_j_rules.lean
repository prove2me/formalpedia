-- Prove2me | solution 1 for Formalism.L2.Th1.F.hecke_kernel_j_rules
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:22:14.707565+00:00
-- url     : https://prove2.me/submissions/962b12b3-66ce-4e40-aefc-a5659d5fe8cb

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelLineZero
import Theorems.Thm_Formalism_L2_Th1_F_Hk3_J_rec
import Theorems.Thm_Formalism_L2_Th1_F_Hk3_J_one
import Theorems.Thm_Formalism_L2_Th1_F_Hk3_J_tendsto

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Filter MeasureTheory
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
namespace Formalism.L2.Th1.F
theorem _root_.solution : HkJRules := ⟨fun _ ha => Hk3.J_rec ha, Hk3.J_one, Hk3.J_tendsto⟩
end Formalism.L2.Th1.F
