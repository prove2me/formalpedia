-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Cnt.kernel_counting_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:20:57.521913+00:00
-- url     : https://prove2.me/submissions/c9321188-7c77-4080-8887-7d493efa03f0

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscOnto
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiagMulMulDiagApply
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscriminantGroupCounts
import Theorems.Thm_Formalism_L2_SG_Pf_discriminantGroupCounts_kerCount_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Cnt
namespace Formalism.L2.SG.Pf.Cnt
theorem _root_.solution : Formalism.L2.SG.Pf.G5.KerCount := by
  intro K F _ _ _ _ _ _ _ hK 𝔭 h𝔭 m a ha0 k hk N hN
  exact Formalism.L2.SG.Pf.discriminantGroupCounts.kerCount_main hK h𝔭 ha0 hk N hN
end Formalism.L2.SG.Pf.Cnt
