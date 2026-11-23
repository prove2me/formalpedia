-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr10.free_l
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:41.903602+00:00
-- url     : https://prove2.me/submissions/c1a88dd4-d9fc-4fda-a9e3-e14c2b4cd726

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommuteInvLeft
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinusLetterFrameOfData
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_free_io
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_free_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_free_add

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
theorem _root_.solution {b : S} (h : f.Free b) (Y : ℂ) : FreeOf b (f.l L Y) :=
  free_add (free_io b _) (free_mul (free_io b _) (h.2.2.2.2.2.2.2.2 Y))
end Formalism.FourierDecayAlt.P.Fr10
