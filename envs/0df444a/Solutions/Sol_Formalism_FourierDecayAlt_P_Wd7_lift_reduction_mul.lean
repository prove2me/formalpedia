-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd7.lift_reduction_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:49:22.623634+00:00
-- url     : https://prove2.me/submissions/ef21a977-2712-4d1c-b4a7-eb96249f3c52

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd7
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd7
theorem _root_.solution (M N : M2 A) : (lift0 (M * N) : M2 (SlopeTestRemainingChoices S A)) = lift0 M * lift0 N := by
  have h : (io : A → SlopeTestRemainingChoices S A) = ⇑(Matrix.scalar (Ix S)) := rfl
  unfold lift0
  rw [h, Matrix.map_mul]
end Formalism.FourierDecayAlt.P.Wd7
