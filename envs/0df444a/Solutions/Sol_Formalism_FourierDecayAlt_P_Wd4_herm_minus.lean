-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd4.herm_minus
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:46:21.142804+00:00
-- url     : https://prove2.me/submissions/b0ee7f00-9ba0-446b-8f98-aa263c68704b

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
variable {K B : Type} [Field K] [StarRing K] [Ring B] [StarRing B] [Algebra K B] [StarModule K B]
  {e : Fin 2 → Fin 2 → B}
namespace Formalism.FourierDecayAlt.P.Wd4
theorem _root_.solution (G Tb T0 Rh : M2 B) (hG : Gᴴ = G) (hGTb : (G * Tb)ᴴ = G * Tb)
    (hGT0 : (G * T0)ᴴ = G * T0) (hRh : Rhᴴ = Rh) (hc : Rh * G = G * Rh)
    (hex : Tb * Rh * T0 = T0 * Rh * Tb) : (G * Tb * (Rh * T0))ᴴ = G * Tb * (Rh * T0) := by
  calc (G * Tb * (Rh * T0))ᴴ = T0ᴴ * Rhᴴ * (G * Tb)ᴴ := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul Rh T0]
    _ = T0ᴴ * (Rh * G) * Tb := by rw [hRh, hGTb]; simp only [mul_assoc]
    _ = (T0ᴴ * Gᴴ) * Rh * Tb := by rw [hc, hG]; simp only [mul_assoc]
    _ = G * (T0 * Rh * Tb) := by rw [← Matrix.conjTranspose_mul, hGT0]; simp only [mul_assoc]
    _ = G * Tb * (Rh * T0) := by rw [← hex]; simp only [mul_assoc]
end Formalism.FourierDecayAlt.P.Wd4
