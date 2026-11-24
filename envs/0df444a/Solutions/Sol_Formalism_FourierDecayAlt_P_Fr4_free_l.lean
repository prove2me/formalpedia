-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr4.free_l
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:56:03.948822+00:00
-- url     : https://prove2.me/submissions/c4157831-cea2-43ce-816e-53720ff50007

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeOf2RmatrixTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_free_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_free_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_free_io

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
theorem _root_.solution (L : LevelData A r) {f : FrameData S A} {c : S} (h : f.Free c) (Y : ℂ) : FreeOf c (f.l L Y) :=
  free_add (free_io c _) (free_mul (free_io c _) (h.2.2.2.2.2.2.2.2 Y))
end Formalism.FourierDecayAlt.P.Fr4
