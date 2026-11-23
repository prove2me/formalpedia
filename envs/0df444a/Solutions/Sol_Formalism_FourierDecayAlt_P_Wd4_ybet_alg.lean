-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd4.ybet_alg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:46:21.304644+00:00
-- url     : https://prove2.me/submissions/a90b2537-68a5-4f51-a226-8f27d90f8297

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd4
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.W
variable {K B : Type} [Field K] [Ring B] [Algebra K B]
variable {e : Fin 2 → Fin 2 → B}
namespace Formalism.FourierDecayAlt.P.Wd4
theorem _root_.solution {C : Type} [Ring C] [Algebra K C] (p12 q13 q23 : C) (d' d : K)
    (g1 : p12 * q13 = q23 * p12) (g2 : p12 * q23 = q13 * p12)
    (g3 : q13 * q23 = q13 * p12) (g4 : q23 * q13 = q23 * p12) :
    ((d - d') • (1 : C) - p12) * (d' • (1 : C) - q13) * (d • (1 : C) - q23) =
      (d • (1 : C) - q23) * (d' • (1 : C) - q13) * ((d - d') • (1 : C) - p12) := by
  have tri : q23 * p12 * q23 = q23 * p12 * p12 := by
    rw [mul_assoc, g2, ← mul_assoc, g4]
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_sub,
    g1, g2, g3, g4, tri]
  module
end Formalism.FourierDecayAlt.P.Wd4
