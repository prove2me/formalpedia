-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr4.freeOf2_matrix_entries
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:36:03.21474+00:00
-- url     : https://prove2.me/submissions/16abcf77-ce9c-4682-a067-acc57b109a5c

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeOf2RmatrixTranspose

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
variable {A S : Type} [Ring A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Fr4
theorem _root_.solution {c : S} {x y z w : SlopeTestRemainingChoices S A} (hx : FreeOf c x) (hy : FreeOf c y) (hz : FreeOf c z)
    (hw : FreeOf c w) : FreeOf2 c !![x, y; z, w] := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact hx
  · exact hy
  · exact hz
  · exact hw
end Formalism.FourierDecayAlt.P.Fr4
