-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x4.pow_mul_pow_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:39:35.8684+00:00
-- url     : https://prove2.me/submissions/d90edb88-67a9-4f9e-aa0b-2b405d6ceed1

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x4
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.A6x4
theorem _root_.solution {p q : K} (hpq : p * q = 1) (m : ℕ) : p ^ m * q ^ m = 1 := by
  rw [← mul_pow, hpq, one_pow]
end Formalism.FourierDecayAlt.P.A6x4
