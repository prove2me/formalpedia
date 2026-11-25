-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.En.coefficient_vector_locality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:31:50.537624+00:00
-- url     : https://prove2.me/submissions/a45cd17e-550c-46ec-8f72-546808eb88c9

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutEnCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutEnCVLocal
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_En_rw_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_capelli_word_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.En
namespace Formalism.FourierDecayAlt.P.CutMP.En
theorem _root_.solution : CVLocal := by
  intro k r E _ _ U f₁ f₂ Y hU h₁ h₂ he g hg
  obtain ⟨L, hL, hCV⟩ := Formalism.FourierDecayAlt.P.capelli_word_sum k r Y
  rw [hCV E (U ∩ B.GV k r) f₁ h₁ g hg hg.2, hCV E (U ∩ B.GV k r) f₂ h₂ g hg hg.2]
  congr 1
  refine List.map_congr_left fun cw hcw => ?_
  rw [rw_congr hU (fun x hx hxG => he x ⟨hx, hxG⟩) cw.2 (fun X hX => ((hL cw hcw).1 X hX).1) g hg.1 hg.2]
end Formalism.FourierDecayAlt.P.CutMP.En
