-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecursionWithDensities.B1.afterOfOld
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:52.440018+00:00
-- url     : https://prove2.me/submissions/73549c5f-d7af-410d-bd63-96927a0c52fa

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_B1_domMinOfText

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data Formalism.FourierDecayAlt.TC
open scoped ComplexOrder
open Classical
variable {E W : Type} [Field E]
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
theorem _root_.solution : AfterOfOld := by
  intro E W _ D hKer hA
  obtain ⟨hKr, hTh⟩ := hKer
  have hT : ∀ T : Tower E, DomText D T D.Th := by
    intro T i s hs hsi hi
    obtain ⟨_, h2, h3, h4⟩ := hA i s hs hsi hi
    have hL : ∀ h ∈ T.X (i - s), level h = i - s := fun h hh => ((T.isTower (i - s) h).mp hh).1
    exact ⟨fun t => hTh i s t _, fun t ht => h2 t ht _ hL,
      fun t t' hl h _ h' _ => by rw [h3 t t' hl], fun S hS => h4 S hS _ hL⟩
  exact ⟨hKr, fun i hi1 hi => (hA i 1 le_rfl hi1 hi).1, hT,
    fun T => ⟨D.Th, domMinOfText E W D T D.Th (hT T)⟩⟩
end Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
