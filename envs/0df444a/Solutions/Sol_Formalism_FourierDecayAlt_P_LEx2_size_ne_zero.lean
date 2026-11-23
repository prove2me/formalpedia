-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.size_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:08.284928+00:00
-- url     : https://prove2.me/submissions/4ff3a665-31dd-497e-8791-6f914c27e418

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
theorem _root_.solution (S : Sys) (hR : S.RootsOut) (w : List (Bool × ℝ)) (hA : S.admitted w) : S.size w ≠ 0 := by
  unfold Sys.size
  apply List.prod_ne_zero
  intro h0
  rw [List.mem_map] at h0
  obtain ⟨x, hx, hx0⟩ := h0
  have hP : S.P x.2 = 0 := abs_eq_zero.mp hx0
  unfold Sys.P at hP
  rw [Finset.prod_eq_zero_iff] at hP
  obtain ⟨s, _, hs⟩ := hP
  apply hR s
  have : -S.lam s = x.2 := by linarith
  rw [this]
  exact hA.1 x hx
end Formalism.FourierDecayAlt.P.LEx2
