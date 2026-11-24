-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.C2x2.lt_bt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:02:17.928953+00:00
-- url     : https://prove2.me/submissions/be33d3d4-4f5a-44b5-9722-48cdb99779b2

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.C2x2
variable {m : ℕ}
namespace Formalism.FourierDecayAlt.P.C2x2
theorem _root_.solution {l : Matrix (Fin m) (Fin m) ℂ} (hl : l ∈ C2.LTset m) : l.BlockTriangular OrderDual.toDual :=
  fun i j h => hl.1 i j (OrderDual.toDual_lt_toDual.mp h)
end Formalism.FourierDecayAlt.P.C2x2
