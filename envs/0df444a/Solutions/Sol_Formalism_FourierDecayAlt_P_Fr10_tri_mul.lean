-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr10.tri_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:07.480804+00:00
-- url     : https://prove2.me/submissions/15419860-98d4-49b4-ba3c-f430bd74b29c

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommuteInvLeft
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinusLetterFrameOfData
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_io_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_io_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_diag_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_diag_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr10
open Formalism.FourierDecayAlt.P.Wd1
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
variable {r : ℕ} (L : LevelData A r) (f : FrameData S A)
namespace Formalism.FourierDecayAlt.P.Fr10
theorem _root_.solution (m : SlopeTestRemainingChoices S A) :
    (!![io L.ζbi, 0; 0, io L.ζi] * !![1, 0; io L.GG * m, io L.GG]) *
      (!![1, 0; -m, io L.GGi] * !![io L.ζb, 0; 0, io L.ζ]) = (1 : M2 (SlopeTestRemainingChoices S A)) := by
  have h1 : (!![1, 0; io L.GG * m, io L.GG] * !![1, 0; -m, io L.GGi] : M2 (SlopeTestRemainingChoices S A)) = 1 := by
    rw [Matrix.mul_fin_two, ← diag_one]
    simp [← io_mul, L.GG_GGi, io_one]
  calc _ = !![io L.ζbi, 0; 0, io L.ζi] * ((!![1, 0; io L.GG * m, io L.GG] * !![1, 0; -m, io L.GGi]) *
        !![io L.ζb, 0; 0, io L.ζ]) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1, Matrix.one_mul, diag_mul, ← io_mul, ← io_mul, L.ζbi_ζb, L.ζi_ζ, io_one, diag_one]
end Formalism.FourierDecayAlt.P.Fr10
