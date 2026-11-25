-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.En.fibre_membership_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:31:54.788679+00:00
-- url     : https://prove2.me/submissions/1e901359-f822-4eb7-bcde-769317bb7d13

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutEnCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutEnFibMem
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_CutMP_En_om_sub__2fc4dbc9d380
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_En_stab_fix_gq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellHermitian_gqDom
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res



set_option autoImplicit false
open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.En
namespace Formalism.FourierDecayAlt.P.CutMP.En
theorem _root_.solution : FibMem := by
  unfold FibMem
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T v hP J hJ q hq
  simp only [NF.Fib, Set.mem_setOf_eq]
  intro p hp
  have hdom : q ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := by
    obtain ⟨hq1, hq2⟩ := hq
    refine ⟨hq1, ?_⟩
    rw [hP.2.2.2.1, hP.2.2.2.2.1]
    exact hq2
  have hg := om_sub' (Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hdom)
  have hfix := stab_fix_gq (T v).base.μsec q hp
  have hJe := hJ.2.2.2 (B.gq (T v).base q) ⟨hg.1, hg.2⟩ p.1 hp.1 p.2 hp.2.1
  exact hJe.symm.trans (congrArg J hfix)
end Formalism.FourierDecayAlt.P.CutMP.En
