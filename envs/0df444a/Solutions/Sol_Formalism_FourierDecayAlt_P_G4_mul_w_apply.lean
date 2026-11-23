-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G4.mul_w_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:08.48097+00:00
-- url     : https://prove2.me/submissions/dc16f820-42f7-450f-9984-ebb9966bdc35

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.FourierDecayAlt.G
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G4
namespace Formalism.FourierDecayAlt.P.G4
theorem _root_.solution {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    (M * wMat d) i j = M i j.rev := by
  have : ∀ k : Fin d, (j = k.rev) = (k = j.rev) := fun k =>
    propext ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [h, Fin.rev_rev]⟩
  simp [wMat, Matrix.mul_apply, this]
end Formalism.FourierDecayAlt.P.G4
