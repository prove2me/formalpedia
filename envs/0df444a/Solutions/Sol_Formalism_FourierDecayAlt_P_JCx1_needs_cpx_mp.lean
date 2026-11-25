-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JCx1.needs.cpx_mp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:57:17.328611+00:00
-- url     : https://prove2.me/submissions/bba7dfca-e55a-4b0d-b703-c9bca5e1a7fb

import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_JCx1_needs_isEmptyReal__0ad2130fa206
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx2_ee_mp


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
open Formalism.FourierDecayAlt Filter Topology MeasureTheory NumberField
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JCx1 Formalism.FourierDecayAlt.P.JCx1.needs
noncomputable section
open scoped Classical
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
namespace Formalism.FourierDecayAlt.P.JCx1.needs
theorem _root_.solution : MeasurePreserving (cpx E) volume volume := by
  haveI := isEmptyReal' E
  have h1 : MeasurePreserving (Formalism.FourierDecayAlt.P.Jx2.ee E) volume volume := by
    first
    | exact Formalism.FourierDecayAlt.P.Jx2.ee_mp E
    | exact Formalism.FourierDecayAlt.P.Jx2.ee_mp
  haveI : IsProbabilityMeasure (volume : Measure ({w : InfinitePlace E // w.IsReal} → ℝ)) := by
    constructor
    rw [MeasureTheory.volume_pi, Measure.pi_of_empty]
    simp
  have h2 : MeasurePreserving (Prod.snd : NumberField.mixedEmbedding.mixedSpace E → _) volume volume :=
    measurePreserving_snd
  exact h2.comp h1
end Formalism.FourierDecayAlt.P.JCx1.needs
