-- Prove2me | solution 1 for Formalism.L2.SG.Pf.GluingBases.glueAssemble_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:38:53.451617+00:00
-- url     : https://prove2.me/submissions/9b289974-7757-448f-92be-02941165deef

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_LeDualFOfGram
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_GlueLocalOfFam
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_isLattice_span
import Theorems.Thm_Formalism_L2_SG_Pf_GluingBases_isLattice_span
import Theorems.Thm_Formalism_L2_SG_Pf_GluingBases_le_dualF_of_gram


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.GluingBases
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU
namespace Formalism.L2.SG.Pf.GluingBases
theorem _root_.solution (h0 : FamTop) (h1 : FamGram) (h2 : FamDual) (h3 : FamMeet) :
    GlueAssemble := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg
  refine ⟨locF 𝔭 (Submodule.span (𝓞 K) (Set.range (glueFam K 𝔭 b a π w τ))),
    ⟨_, isLattice_span _ (h0 K F V hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg), rfl⟩,
    le_antisymm (h2 K F V hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg)
      (le_dualF_of_gram hF h h𝔭.isPrime _ (h1 K F V hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg)),
    h3 K F V hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg⟩
end Formalism.L2.SG.Pf.GluingBases
