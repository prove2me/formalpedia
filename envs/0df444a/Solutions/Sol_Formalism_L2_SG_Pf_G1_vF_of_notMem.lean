-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G1.vF_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:47.956325+00:00
-- url     : https://prove2.me/submissions/80d48bdb-1292-49d6-a864-ebc3956cab3b

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsOrthGen
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsFracOfFixed
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_AlmostEverywhereSpherical
import Theorems.Thm_Formalism_L2_SG_Pf_G1_mem_pow_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mem_pow_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G1
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA
variable {F : Type} [Field F] [NumberField F] {𝔭 : Ideal (𝓞 F)}
namespace Formalism.L2.SG.Pf.G1
theorem _root_.solution (h𝔭 : 𝔭.IsMaximal) {t : 𝓞 F} (ht : t ∉ 𝔭) : vF 𝔭 t = 0 := by
  have ht0 : t ≠ 0 := fun h => ht (h ▸ 𝔭.zero_mem)
  have h1 := (mem_pow_iff h𝔭 ht0 1).not.mp (by rwa [pow_one])
  omega
end Formalism.L2.SG.Pf.G1
