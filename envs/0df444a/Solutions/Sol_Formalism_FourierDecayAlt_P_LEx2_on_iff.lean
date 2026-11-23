-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.on_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:52.972253+00:00
-- url     : https://prove2.me/submissions/c71d9d4d-8e76-44f3-b5db-2cb6cfccdcf5

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DegreeOfProdLinearLe
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_onBoxes_ofFn

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
theorem _root_.solution (S : Sys) (N : ℕ) (Y : Fin N → ℝ) : (S.fam N).On Y ↔ S.OnBoxes (List.ofFn Y) := by
  rw [onBoxes_ofFn]
  unfold Fam.On
  constructor
  · intro h a; have := h a; rw [S.fam_J] at this; exact this
  · intro h a; rw [S.fam_J]; exact h a
end Formalism.FourierDecayAlt.P.LEx2
