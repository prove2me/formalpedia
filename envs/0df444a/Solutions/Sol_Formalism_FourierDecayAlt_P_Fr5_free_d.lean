-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr5.free_d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:43:36.742644+00:00
-- url     : https://prove2.me/submissions/ae64b0c4-15d7-4b37-a259-9ecd6516e103

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeOf2OfFourEntries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_free_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_free_pow
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_free_wt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr5
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Fr5
theorem _root_.solution (L : LevelData A r) (f : FrameData S A) {a : S} (h : f.Free a) : FreeOf a (f.d L) := by
  obtain ⟨-, -, -, -, -, -, hc, -, -⟩ := h
  exact free_mul (free_pow (free_wt L a) _) hc
end Formalism.FourierDecayAlt.P.Fr5
