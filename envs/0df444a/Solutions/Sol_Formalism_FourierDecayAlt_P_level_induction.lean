-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.level_induction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:42:59.977342+00:00
-- url     : https://prove2.me/submissions/1628f06d-e742-478d-9969-67ff747b0398

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShiftBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DegreeOfProdLinearLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Cauchy
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivedCoefficientIntegrable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
private theorem le_claimInduction_proof : Formalism.FourierDecayAlt.LE.ClaimInduction := by
  intro S hJL2 hstep w
  induction w with
  | nil =>
    intro _ _
    refine ⟨hJL2, ?_⟩
    simp only [Formalism.FourierDecayAlt.LE.Sys.size, Formalism.FourierDecayAlt.LE.plus, List.map_nil, List.prod_nil, one_mul]
    rfl
  | cons Y w ih =>
    intro hOn hlen
    have hOn' : Y ∈ S.box w.length ∧ S.OnBoxes w := hOn
    have hlen' : w.length < S.Ntot := by
      simp only [List.length_cons] at hlen
      omega
    obtain ⟨hi, he⟩ := ih hOn'.2 hlen'.le
    have h := hstep w Y hOn hlen' hi
    refine ⟨h.1, ?_⟩
    rw [h.2, he]
    simp only [Formalism.FourierDecayAlt.LE.Sys.size, Formalism.FourierDecayAlt.LE.plus, List.map_cons, List.prod_cons]
    ring
end Formalism.FourierDecayAlt.P.LEx2
end

set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.LE.ClaimInduction := Formalism.FourierDecayAlt.P.LEx2.le_claimInduction_proof
end Formalism.FourierDecayAlt.P
