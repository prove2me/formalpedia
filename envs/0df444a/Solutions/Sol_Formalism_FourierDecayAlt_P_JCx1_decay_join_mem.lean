-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JCx1.decay.join_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:05:46.956513+00:00
-- url     : https://prove2.me/submissions/39363b5d-7a60-4b4c-b504-9dfdac1ede02

import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_B1_decay


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt
open Finset Formalism.FourierDecayAlt
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JCx1 Formalism.FourierDecayAlt.P.JCx1.decay
open Formalism.FourierDecayAlt.TB
open scoped ComplexOrder
attribute [local instance] Classical.propDecidable
variable {E W : Type} [Field E] (D : Data E W)
namespace Formalism.FourierDecayAlt.P.JCx1.decay
theorem _root_.solution (Y : Finset (Pt E)) (s : ℕ) (T : Finset E) (t : E) (ht : t ∈ T) :
    ∀ h ∈ Y, join h s t ∈ pts Y s T := by
  intro h hh
  unfold pts
  exact Finset.mem_image.2 ⟨(h, t), Finset.mem_product.2 ⟨hh, ht⟩, rfl⟩
end Formalism.FourierDecayAlt.P.JCx1.decay
