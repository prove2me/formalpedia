-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux5.wMat_ct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:34:54.348173+00:00
-- url     : https://prove2.me/submissions/e40fc84f-01ea-423b-b1f7-ce414246f9a2

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetNormLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux5
namespace Formalism.FourierDecayAlt.P.Ux5
theorem _root_.solution (d : ℕ) : (G.wMat d)ᴴ = G.wMat d := by
  ext i j
  simp only [G.wMat, conjTranspose_apply, of_apply]
  by_cases h : j = i.rev
  · subst h
    simp [Fin.rev_rev]
  · have h' : ¬ i = j.rev := fun h'' => h (by rw [h'', Fin.rev_rev])
    simp [h, h']
end Formalism.FourierDecayAlt.P.Ux5
