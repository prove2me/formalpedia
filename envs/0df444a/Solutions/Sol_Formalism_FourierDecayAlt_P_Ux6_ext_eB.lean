-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux6.ext_eB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:55:26.642691+00:00
-- url     : https://prove2.me/submissions/5d4bf815-7e97-4150-836d-f5b76a0e1004

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
theorem _root_.solution {M N : B.Mat k (j + ρ)} (h : ∀ x y : Ix k j ρ, M (eB k j ρ x) (eB k j ρ y) = N (eB k j ρ x) (eB k j ρ y)) :
    M = N := by
  ext i b
  have := h ((eB k j ρ).symm i) ((eB k j ρ).symm b)
  simpa using this
end Formalism.FourierDecayAlt.P.Ux6
