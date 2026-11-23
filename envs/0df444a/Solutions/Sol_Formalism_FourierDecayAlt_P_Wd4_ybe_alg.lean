-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd4.ybe_alg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:46:21.227553+00:00
-- url     : https://prove2.me/submissions/f84a6e8e-be6c-4134-8fc6-d0b864866fa2

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
theorem _root_.solution {C : Type} [Ring C] [Algebra K C] (p12 p13 p23 : C) (u v : K)
    (h1 : p13 * p23 = p12 * p13) (h2 : p23 * p12 = p12 * p13)
    (h3 : p23 * p13 = p12 * p23) (h4 : p13 * p12 = p12 * p23) :
    ((u - v) • (1 : C) - p12) * (u • (1 : C) - p13) * (v • (1 : C) - p23) =
      (v • (1 : C) - p23) * (u • (1 : C) - p13) * ((u - v) • (1 : C) - p12) := by
  have tri : p12 * p13 * p23 = p12 * p23 * p12 := by
    calc p12 * p13 * p23 = p23 * p12 * p23 := by rw [h2]
      _ = p23 * (p13 * p12) := by rw [mul_assoc, h4]
      _ = p12 * p23 * p12 := by rw [← mul_assoc, h3]
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_sub,
    h1, h2, h3, h4, tri]
  module
end Formalism.FourierDecayAlt.P.Wd4
