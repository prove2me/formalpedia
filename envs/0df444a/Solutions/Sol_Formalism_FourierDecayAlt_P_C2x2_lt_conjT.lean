-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.C2x2.lt_conjT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:02:19.4542+00:00
-- url     : https://prove2.me/submissions/1473d214-2f07-4aa0-8d3d-318eb84e77bc

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
theorem _root_.solution {l : Matrix (Fin m) (Fin m) ℂ} (hl : l ∈ C2.LTset m) : lᴴ ∈ C2.UTset m :=
  ⟨fun i j h => by rw [Matrix.conjTranspose_apply, hl.1 j i h, star_zero],
   fun i => by rw [Matrix.conjTranspose_apply, hl.2, star_one]⟩
end Formalism.FourierDecayAlt.P.C2x2
