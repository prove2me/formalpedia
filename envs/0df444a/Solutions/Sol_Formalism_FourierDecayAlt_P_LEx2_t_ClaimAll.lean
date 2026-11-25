-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.t_ClaimAll
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:35:08.947077+00:00
-- url     : https://prove2.me/submissions/6ac41511-4d13-4b26-b6a7-c7ae6b77a530

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DegreeOfProdLinearLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution : ClaimAll := by
  intro hStep hInd S σ CR Cd CP hσ h1 h2 h3 hL hLL hJ hSI
  apply hInd S hJ
  intro w Y hOn hlen hint
  have hY : Y ∈ (S.step w).J := by
    have := hOn.1
    simpa [Step.J, Sys.box, S.step_a, S.step_L] using this
  have h := hStep S.B (S.step w) S.c σ CR Cd CP hσ h1 h2 h3 (by rw [S.step_L]; exact hL)
    (by rw [S.step_L, S.step_r]; exact hLL) (hSI w hOn.2 hlen) hint Y hY
  have e : S.dens (Y :: w) = LE.sq S.B ((S.step w).d Y) ((S.step w).gX Y) := by
    funext ω; exact S.step_new w Y ω
  rw [e]
  refine ⟨h.1, ?_⟩
  rw [h.2, S.step_P]
  rfl
end Formalism.FourierDecayAlt.P.LEx2
