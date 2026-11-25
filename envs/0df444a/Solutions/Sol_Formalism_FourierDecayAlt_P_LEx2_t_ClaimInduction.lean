-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.t_ClaimInduction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:47:31.064748+00:00
-- url     : https://prove2.me/submissions/e78c3fd1-dbc9-493e-b241-3b6a2e4d645f

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
theorem _root_.solution : ClaimInduction := by
  intro S hJ hstep w
  induction w with
  | nil =>
    intro _ _
    refine ⟨hJ, ?_⟩
    simp [Sys.size, plus, Sys.jn]
  | cons Y w ih =>
    intro hOn hlen
    have hlen' : w.length < S.Ntot := by simpa [Nat.succ_le_iff] using hlen
    have hc := ih hOn.2 hlen'.le
    have h := hstep w Y hOn hlen' hc.1
    refine ⟨h.1, ?_⟩
    rw [h.2, hc.2]
    simp [Sys.size, plus]
    ring
end Formalism.FourierDecayAlt.P.LEx2
