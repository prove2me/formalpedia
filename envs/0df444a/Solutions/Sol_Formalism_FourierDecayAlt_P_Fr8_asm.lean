-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr8.asm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:07:54.795627+00:00
-- url     : https://prove2.me/submissions/08289946-2902-4671-9336-c0efd7921637

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussFormMinusLetter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr8
namespace Formalism.FourierDecayAlt.P.Fr8
theorem _root_.solution {R : Type} [Ring R] [StarRing R] {F Fi d U D Λ : R} (hFFi : F * Fi = 1)
    (hU : d * U = star Λ * d) :
    star F * d * F * (Fi * (U * D * Λ) * F) = star (Λ * F) * (d * D) * (Λ * F) := by
  rw [star_mul]
  calc star F * d * F * (Fi * (U * D * Λ) * F) = star F * d * (F * Fi) * U * D * Λ * F := by
        simp only [mul_assoc]
    _ = star F * (d * U) * D * Λ * F := by rw [hFFi, mul_one]; simp only [mul_assoc]
    _ = star F * star Λ * (d * D) * (Λ * F) := by rw [hU]; simp only [mul_assoc]
end Formalism.FourierDecayAlt.P.Fr8
