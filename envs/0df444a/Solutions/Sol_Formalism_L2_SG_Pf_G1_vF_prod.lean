-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G1.vF_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:18:34.08626+00:00
-- url     : https://prove2.me/submissions/b9c74096-4f1e-422d-85c1-8e55808cbd2b

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsOrthGen
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsFracOfFixed
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_AlmostEverywhereSpherical
import Theorems.Thm_Formalism_L2_SG_Pf_G1_vF_mul
import Theorems.Thm_Formalism_L2_SG_Pf_G1_vF_of_notMem

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
theorem _root_.solution (h𝔭 : 𝔭.IsMaximal) {ι : Type*} (s : Finset ι) (f : ι → 𝓞 F) (hf : ∀ i, f i ≠ 0) :
    vF 𝔭 (∏ i ∈ s, f i) = ∑ i ∈ s, vF 𝔭 (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, Finset.sum_empty]
    exact vF_of_notMem h𝔭 (fun h => h𝔭.ne_top ((Ideal.eq_top_iff_one _).mpr h))
  · intro i s hi ih
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      vF_mul h𝔭 (hf i) (Finset.prod_ne_zero_iff.mpr fun j _ => hf j), ih]
end Formalism.L2.SG.Pf.G1
