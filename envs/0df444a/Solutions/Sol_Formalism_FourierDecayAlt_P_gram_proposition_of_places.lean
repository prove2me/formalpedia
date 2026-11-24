-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.gram_proposition_of_places
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:55:52.649041+00:00
-- url     : https://prove2.me/submissions/d22e8dcc-9d20-4be2-8729-ea9dbd3699da

import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_needs_ptSize_loc

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.JC.PropGramOfPlaces := by
  intro E _ _ _ Wp Wq _ _ _ _ S Hv _ _ V H _ _ Vt hT hG Y hY
  have hv : ∀ v, ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ p ∈ Y.image (C.loc (S.σ v)), ∀ q ∈ Y.image (C.loc (S.σ v)),
      (S.pd v).RR ε (S.G.r + 1) [] p q = inner ℂ (V v q) (V v p) := by
    intro v
    apply hG v
    intro p hp
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hp
    rw [Formalism.FourierDecayAlt.P.JCx1.needs.ptSize_loc]
    exact (hY p' hp').1
  filter_upwards [Filter.eventually_all.mpr hv] with ε hε
  intro p hp q hq
  rw [hT p q (hY p hp) (hY q hq)]
  simp only [C.HidaSetting.gram, le_refl, if_true, C.HidaSetting.gramLoc, C.Word.emp]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [hε v _ (Finset.mem_image_of_mem _ hp) _ (Finset.mem_image_of_mem _ hq)]
end Formalism.FourierDecayAlt.P
