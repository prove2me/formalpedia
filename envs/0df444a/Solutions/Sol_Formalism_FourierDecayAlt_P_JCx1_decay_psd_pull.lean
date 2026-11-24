-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JCx1.decay.psd_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:55:10.552106+00:00
-- url     : https://prove2.me/submissions/ed6885f3-63a7-41d7-ad02-b1fecfa1e4c5

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
namespace Formalism.FourierDecayAlt.P.JCx1.decay
theorem _root_.solution {Z X : Type} [DecidableEq Z] (P : Finset Z) (H : Z → Z → ℂ) (hH : PSDOn P H)
    (Y : Finset X) (g : X → Z) (hg : ∀ h ∈ Y, g h ∈ P) : PSDOn Y (fun x y => H (g x) (g y)) := by
  have hH' : Matrix.PosSemidef (Matrix.of fun x y : P => H x y) := hH
  exact hH'.submatrix (fun y : Y => (⟨g y, hg y y.2⟩ : P))
end Formalism.FourierDecayAlt.P.JCx1.decay
