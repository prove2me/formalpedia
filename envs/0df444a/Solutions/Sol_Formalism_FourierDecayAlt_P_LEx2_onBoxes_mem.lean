-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.onBoxes_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:52.798655+00:00
-- url     : https://prove2.me/submissions/80a31182-5602-4f38-9a2d-29f10146a49b

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
theorem _root_.solution (S : Sys) : ∀ w : List ℝ, S.OnBoxes w → ∀ y ∈ w, ∃ a, a < w.length ∧ y ∈ S.box a := by
  intro w
  induction w with
  | nil => intro _ y hy; simp at hy
  | cons Y w ih =>
    intro h y hy
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact ⟨w.length, by simp, h.1⟩
    · obtain ⟨a, ha, hm⟩ := ih h.2 y hy'
      exact ⟨a, by simp; omega, hm⟩
end Formalism.FourierDecayAlt.P.LEx2
