-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr4.free_m
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:11.900031+00:00
-- url     : https://prove2.me/submissions/43fbe7df-dfa9-4995-8494-74e7973adaeb

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeOf2RmatrixTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_free_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_free_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_free_l
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_free_d
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_free_di

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr4
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Fr4
theorem _root_.solution (L : LevelData A r) {f : FrameData S A} {c : S} (h : f.Free c) (Y : ℂ) : FreeOf c (f.m L Y) :=
  free_mul (free_mul (free_di L h) (free_star (free_l L h _))) (free_d L h)
end Formalism.FourierDecayAlt.P.Fr4
