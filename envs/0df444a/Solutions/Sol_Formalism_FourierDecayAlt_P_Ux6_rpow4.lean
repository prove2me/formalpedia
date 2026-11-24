-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux6.rpow4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:42:23.926334+00:00
-- url     : https://prove2.me/submissions/e1b99aad-763a-4524-95dc-c2f0df6e119b

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
namespace Formalism.FourierDecayAlt.P.Ux6
theorem _root_.solution {A B C D a : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    (A * B * C * D) ^ (-a) = (A ^ (-a) * B ^ (-a)) * (C ^ (-a) * D ^ (-a)) := by
  rw [Real.mul_rpow (by positivity) hD, Real.mul_rpow (by positivity) hC, Real.mul_rpow hA hB]
  ring
end Formalism.FourierDecayAlt.P.Ux6
