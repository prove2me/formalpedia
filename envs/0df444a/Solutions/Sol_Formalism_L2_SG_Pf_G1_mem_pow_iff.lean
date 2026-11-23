-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G1.mem_pow_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:10.898941+00:00
-- url     : https://prove2.me/submissions/8bc68abe-cad4-4b98-9f6e-145f425d7991

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsOrthGen
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsFracOfFixed
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_AlmostEverywhereSpherical
import Theorems.Thm_Formalism_L2_SG_Pf_G1_setOf_mem_pow_eq
import Theorems.Thm_Formalism_L2_SG_Pf_G1_vF_eq_multiplicity

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
theorem _root_.solution (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) (e : ℕ) :
    n ∈ 𝔭 ^ e ↔ e ≤ vF 𝔭 n := by
  rw [vF_eq_multiplicity h𝔭 hn, ← Set.mem_Iic, ← setOf_mem_pow_eq h𝔭 hn, Set.mem_setOf_eq]
end Formalism.L2.SG.Pf.G1
