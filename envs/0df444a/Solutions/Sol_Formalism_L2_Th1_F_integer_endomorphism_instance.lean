-- Prove2me | solution 1 for Formalism.L2.Th1.F.integer_endomorphism_instance
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:51:10.593211+00:00
-- url     : https://prove2.me/submissions/43e0c258-c642-4085-8cc1-b780f4d6e947

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IntegerEndomorphismInstance
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_T_neg
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_clause3
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_clause2
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_exists_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
namespace Formalism.L2.Th1.F
theorem _root_.solution : EndoZInstance := by
  intro L α S hα hm hS
  choose neg hneg using EndoZ.exists_neg L α S hS
  refine ⟨neg, hneg, ?_⟩
  unfold Formalism.L2.Th1.C.IsEndoZ
  refine ⟨?_, ?_, ?_⟩
  · intro P
    apply Subtype.ext
    apply hS.2.1 _ (neg (neg P)).2 _ P.2
    have e : ((neg (neg P) : ℂ) - P) = ((neg (neg P) : ℂ) + neg P) - (neg P + P) := by ring
    rw [e]
    exact L.lattice.sub_mem (hneg (neg P)) (hneg P)
  · intro P
    exact EndoZ.clause2 L (hS.1 P P.2).2 (hneg P)
  · exact EndoZ.clause3 L α S hα hm hS
end Formalism.L2.Th1.F
