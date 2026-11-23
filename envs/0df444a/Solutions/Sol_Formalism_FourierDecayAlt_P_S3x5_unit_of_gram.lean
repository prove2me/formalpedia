-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x5.unit_of_gram
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:50:00.932522+00:00
-- url     : https://prove2.me/submissions/ca265e7b-6879-46dd-b1af-f0c971fe24b3

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x5
open Matrix Formalism.FourierDecayAlt.S3
variable {K : Type} [Field K] [Fintype K] [StarRing K]
omit [Fintype K]
namespace Formalism.FourierDecayAlt.P.S3x5
theorem _root_.solution {ν : Type} [Fintype ν] [DecidableEq ν] (J g : Matrix ν ν K) (hd : IsUnit J.det)
    (h : gᴴ * J * g = J) : IsUnit g.det := by
  have : IsUnit ((gᴴ * J).det * g.det) := by rw [← det_mul, h]; exact hd
  exact isUnit_of_mul_isUnit_right this
end Formalism.FourierDecayAlt.P.S3x5
