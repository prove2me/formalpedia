-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Cx2.eLat_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:13:03.440735+00:00
-- url     : https://prove2.me/submissions/2bc760c7-82d9-4fb2-a9aa-57751251dbfc

import Definitions.Def_Formalism_HermitianCurvature_StatementC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelZeroEstimateProduct
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstNormRealNonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Cx2_frame_facts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C NumberField MeasureTheory
open scoped ComplexOrder ComplexConjugate RealInnerProductSpace
noncomputable section
open Formalism.FourierDecayAlt.P.Cx2
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace Formalism.FourierDecayAlt.P.Cx2
theorem _root_.solution (hEF : J.EuclidFrame) (g : ℕ) (hg : 0 < g) (ν : ℤ) :
    ∃ _ : DiscreteTopology (J.eLat E (S6.perLat E g ν 1) 1), IsZLattice ℝ (J.eLat E (S6.perLat E g ν 1) 1) := by
  obtain ⟨hd, hs⟩ := frame_facts (E := E) g hg ν
  obtain ⟨hd', hs', -⟩ := hEF E (S6.perLat E g ν 1) 1 hd hs
  exact ⟨hd', { span_top := hs' }⟩
end Formalism.FourierDecayAlt.P.Cx2
