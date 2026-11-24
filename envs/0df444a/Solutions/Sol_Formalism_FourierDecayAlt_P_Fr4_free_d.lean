-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr4.free_d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:56:06.408925+00:00
-- url     : https://prove2.me/submissions/f9e8b1b8-bf8b-4597-a3b2-519a54b72379

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeOf2RmatrixTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_free_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_free_pow
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
theorem _root_.solution (L : LevelData A r) {f : FrameData S A} {c : S} (h : f.Free c) : FreeOf c (f.d L) :=
  free_mul (free_pow (free_io c _) _) h.2.2.2.2.2.2.1
end Formalism.FourierDecayAlt.P.Fr4
