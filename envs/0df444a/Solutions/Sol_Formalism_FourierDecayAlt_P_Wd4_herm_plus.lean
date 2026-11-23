-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd4.herm_plus
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:46:21.262181+00:00
-- url     : https://prove2.me/submissions/4635d1d2-29fd-48fc-b52c-3f3570835a09

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
theorem _root_.solution (G Ta T0 Rh : M2 B) (hG : Gᴴ = G) (hGTa : (G * Ta)ᴴ = G * Ta)
    (hGT0 : (G * T0)ᴴ = G * T0) (hRh : Rhᴴ = Rh) (hc : Rh * G = G * Rh)
    (hex : Ta * T0 * Rh = Rh * T0 * Ta) : (G * Ta * (T0 * Rh))ᴴ = G * Ta * (T0 * Rh) := by
  calc (G * Ta * (T0 * Rh))ᴴ = Rhᴴ * T0ᴴ * (G * Ta)ᴴ := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul T0 Rh]
    _ = Rh * (T0ᴴ * Gᴴ) * Ta := by rw [hRh, hGTa, hG]; simp only [mul_assoc]
    _ = Rh * (G * T0) * Ta := by rw [← Matrix.conjTranspose_mul, hGT0]
    _ = G * (Rh * T0 * Ta) := by rw [← mul_assoc, hc]; simp only [mul_assoc]
    _ = G * Ta * (T0 * Rh) := by rw [← hex]; simp only [mul_assoc]
end Formalism.FourierDecayAlt.P.Wd4
