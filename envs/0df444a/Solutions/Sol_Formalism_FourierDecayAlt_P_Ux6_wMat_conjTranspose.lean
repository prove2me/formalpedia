-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux6.wMat_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:45:23.224868+00:00
-- url     : https://prove2.me/submissions/539472db-a838-4273-b420-7c4748318580

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux6
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux6
theorem _root_.solution (d : ℕ) : (G.wMat d)ᴴ = G.wMat d := by
  ext i b
  simp only [G.wMat, Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases h : i = b.rev
  · have h' : b = i.rev := by rw [h, Fin.rev_rev]
    rw [if_pos h, if_pos h', star_one]
  · have h' : ¬ b = i.rev := by
      intro h'; apply h; rw [h', Fin.rev_rev]
    rw [if_neg h, if_neg h', star_zero]
end Formalism.FourierDecayAlt.P.Ux6
