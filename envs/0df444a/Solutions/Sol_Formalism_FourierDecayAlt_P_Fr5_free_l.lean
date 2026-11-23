-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr5.free_l
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:51.573432+00:00
-- url     : https://prove2.me/submissions/d647d385-5aa4-437e-b563-d1bffe402a8b

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeOf2OfFourEntries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_free_io
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_free_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_free_add

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
theorem _root_.solution (L : LevelData A r) (f : FrameData S A) {a : S} (h : f.Free a) (Y : ℂ) : FreeOf a (f.l L Y) := by
  obtain ⟨-, -, -, -, -, -, -, -, hee⟩ := h
  exact free_add (free_io a _) (free_mul (free_io a _) (hee Y))
end Formalism.FourierDecayAlt.P.Fr5
