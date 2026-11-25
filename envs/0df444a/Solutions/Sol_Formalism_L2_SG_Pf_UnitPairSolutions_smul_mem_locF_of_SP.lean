-- Prove2me | solution 1 for Formalism.L2.SG.Pf.UnitPairSolutions.smul_mem_locF_of_SP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:50:19.748108+00:00
-- url     : https://prove2.me/submissions/69e49ff5-97a2-4d10-aa97-3fc4c36ff104

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_InPOfMemPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_SmulMemLocFOfSP
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_InP_mem_SP
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_mem_SP


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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.UnitPairSolutions
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU Formalism.L2.SG.Pf.GluingBases
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.L2.SG.Pf.UnitPairSolutions
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} [hp : 𝔭.IsPrime] {L : Submodule (𝓞 K) V} {r : K}
    (hr : r ∈ SP K 𝔭) {v : V} (hv : v ∈ L) : r • v ∈ locF 𝔭 L := by
  obtain ⟨t, ht, z, hz⟩ := mem_SP.mp hr
  refine ⟨algebraMap (𝓞 F) (𝓞 K) t, Submonoid.subset_closure ⟨t, ht, rfl⟩, ?_⟩
  have he : algebraMap (𝓞 F) (𝓞 K) t • r • v = z • v := by
    rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) (r • v), smul_smul, ← hz, algebraMap_smul]
  rw [he]
  exact L.smul_mem z hv
end Formalism.L2.SG.Pf.UnitPairSolutions
