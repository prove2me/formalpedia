-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.minor_C_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:59:16.746258+00:00
-- url     : https://prove2.me/submissions/952f65d7-3cfd-4772-9efe-8e667f3dd2c2

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Theorems.Thm_Formalism_FourierDecayAlt_P_c2x3_iSet_card
import Theorems.Thm_Formalism_FourierDecayAlt_P_c2x3_wSet_card
import Theorems.Thm_Formalism_FourierDecayAlt_P_c2x3_det_mono_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x2
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.MinorCNonzero := by
  intro m w d hd a ha
  have hI := c2x3_wSet_card w ha
  have hJ := c2x3_iSet_card ha
  unfold C2.minorS
  rw [dif_pos (hI.trans hJ.symm)]
  apply c2x3_det_mono_ne w d hd _ _ (RelEmbedding.injective _) (RelEmbedding.injective _)
  intro j
  have hmem : w ((C2.iSet m a).orderEmbOfFin (hI.trans hJ.symm).symm j) ∈ C2.wSet w a :=
    Finset.mem_image_of_mem w (Finset.orderEmbOfFin_mem _ _ j)
  have hr := Finset.range_orderEmbOfFin (C2.wSet w a) (rfl : (C2.wSet w a).card = (C2.wSet w a).card)
  rw [← Finset.mem_coe, ← hr] at hmem
  exact hmem
end Formalism.FourierDecayAlt.P
