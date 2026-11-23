-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr10.free_m
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:04.999147+00:00
-- url     : https://prove2.me/submissions/282aa4c5-e91b-48df-83a3-1b00fc720c82

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommuteInvLeft
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinusLetterFrameOfData
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_free_io
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_free_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_free_pow
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_free_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_free_l

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
theorem _root_.solution {b : S} (h : f.Free b) (Y : ℂ) : FreeOf b (f.m L Y) :=
  free_mul (free_mul (free_mul h.2.2.2.2.2.2.2.1 (free_pow (free_io b _) _)) (free_star (free_l L f h _)))
    (free_mul (free_pow (free_io b _) _) h.2.2.2.2.2.2.1)
end Formalism.FourierDecayAlt.P.Fr10
