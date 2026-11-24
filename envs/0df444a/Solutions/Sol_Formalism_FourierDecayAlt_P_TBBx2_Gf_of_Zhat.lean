-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx2.Gf_of_Zhat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:56:10.525816+00:00
-- url     : https://prove2.me/submissions/e64342e5-33a6-4881-b9c9-ce6e4a09dd7e

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx2
open MeasureTheory Filter Topology Formalism.QuantumDeterminants
open scoped ENNReal
noncomputable section
namespace Formalism.FourierDecayAlt.P.TBBx2
theorem _root_.solution {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) (pt : C.LPt)
    (h : Zhat k r z z' g = D.ptMatN pt (r + 1)) :
    Gf k r z z' g = D.ptG (Tz k r z * Tz k r z') r pt := by
  have e1 : Dmin k r z z' g (Fin.last (r + 1)) = (D.ptMatN pt (r + 1)).det := by
    unfold Dmin
    rw [h]
    try rfl
  have e2 : Dmin k r z z' g ⟨r, by omega⟩ = (D.ptMatN pt r).det := by
    unfold Dmin
    rw [h]
    try rfl
  unfold Gf D.ptG
  rw [e1, e2]
end Formalism.FourierDecayAlt.P.TBBx2
