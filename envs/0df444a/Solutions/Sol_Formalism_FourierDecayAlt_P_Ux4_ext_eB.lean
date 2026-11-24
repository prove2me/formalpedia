-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux4.ext_eB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:53:56.749581+00:00
-- url     : https://prove2.me/submissions/24d044c5-f7d9-4d12-8af6-79fdf10559c9

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
theorem _root_.solution {M N : B.Mat k (j + ρ)} (h : ∀ x y : Ix k j ρ, M (eB k j ρ x) (eB k j ρ y) = N (eB k j ρ x) (eB k j ρ y)) :
    M = N := by
  ext a b
  simpa using h ((eB k j ρ).symm a) ((eB k j ρ).symm b)
end Formalism.FourierDecayAlt.P.Ux4
