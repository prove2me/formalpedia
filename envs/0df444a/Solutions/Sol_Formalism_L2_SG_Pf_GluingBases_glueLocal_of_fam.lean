-- Prove2me | solution 1 for Formalism.L2.SG.Pf.GluingBases.glueLocal_of_fam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:57:47.253607+00:00
-- url     : https://prove2.me/submissions/139bbd70-8e2f-4746-8577-60c151cd1307

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_LeDualFOfGram
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_GlueLocalOfFam
import Theorems.Thm_Formalism_L2_SG_Pf_GluingBases_glueAssemble_of
import Theorems.Thm_Formalism_L2_SG_Pf_GluingBases_glueLocal_of_of


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
theorem _root_.solution (hJ : JordanExists) (hV : GlueVecs) (h0 : FamTop) (h1 : FamGram)
    (h2 : FamDual) (h3 : FamMeet) : Formalism.L2.SG.Pf.G7.GlueLocal :=
  glueLocal_of_of hJ hV (glueAssemble_of h0 h1 h2 h3)
end Formalism.L2.SG.Pf.GluingBases
