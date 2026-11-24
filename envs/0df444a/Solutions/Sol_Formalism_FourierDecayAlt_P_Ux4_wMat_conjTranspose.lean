-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux4.wMat_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:24:22.285889+00:00
-- url     : https://prove2.me/submissions/669c6d24-77a3-47b9-816f-2c321dccfe3b

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux4
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux4
theorem _root_.solution (d : ℕ) : (G.wMat d)ᴴ = G.wMat d := by
  ext a b
  simp only [G.wMat, Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases h : b = a.rev
  · subst h
    simp [Fin.rev_rev]
  · have h' : a ≠ b.rev := by
      intro h'
      apply h
      rw [h', Fin.rev_rev]
    simp [h, h']
end Formalism.FourierDecayAlt.P.Ux4
