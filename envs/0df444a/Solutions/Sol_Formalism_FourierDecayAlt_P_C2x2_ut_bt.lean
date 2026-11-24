-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.C2x2.ut_bt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:02:21.463732+00:00
-- url     : https://prove2.me/submissions/b5742073-7ab0-4985-aa9f-fcdb7821f4b3

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
theorem _root_.solution {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) : u.BlockTriangular id :=
  fun i j h => hu.1 i j h
end Formalism.FourierDecayAlt.P.C2x2
