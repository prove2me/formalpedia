-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.edgeRatios
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:38:07.868853+00:00
-- url     : https://prove2.me/submissions/1e2536ea-cd8e-45c2-b649-0f99fd4bd235

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_prod_ratio_ge
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_a_sub_u_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_kDel_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_edge_ratio_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_bp_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_u_mid_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_top_ratio_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Formalism.FourierDecayAlt.Sz Formalism.FourierDecayAlt.P.Sz4
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Sz.EdgeRatios := by
  intro c de de' hc _ hw hw'
  have hkD := kDel_pos c hc
  refine ⟨⟨?_, edge_ratio_le c de de' hc hw hw'⟩, fun ht => ⟨?_, top_ratio_le c de de' hc ht hw hw'⟩⟩
  · refine prod_ratio_ge _ (fun i => c.a - c.u de i) (fun i => c.a - c.u de' i) _
      (fun i hi => ?_) (fun i hi => ?_) (edge_ratio_le c de' de hc hw' hw)
    · have := a_sub_u_pos c de' hc hw' i hi; linarith
    · have := a_sub_u_pos c de hc hw i hi; linarith
  · have hb := bp_pos c hc ht
    refine prod_ratio_ge _ (fun i => c.u de i + c.bp) (fun i => c.u de' i + c.bp) _
      (fun i hi => ?_) (fun i hi => ?_) (top_ratio_le c de' de hc ht hw' hw)
    · have := u_mid_nonneg c de' hc hw' i hi; linarith
    · have := u_mid_nonneg c de hc hw i hi; linarith
end Formalism.FourierDecayAlt.P
