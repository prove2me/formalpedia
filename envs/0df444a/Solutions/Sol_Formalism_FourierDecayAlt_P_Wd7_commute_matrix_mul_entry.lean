-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd7.commute_matrix_mul_entry
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:49:56.466113+00:00
-- url     : https://prove2.me/submissions/f152eaca-bfad-4776-a70f-97517afaebf0

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
theorem _root_.solution {b : SlopeTestRemainingChoices S A} {M N : M2 (SlopeTestRemainingChoices S A)} (hM : ∀ i j, Commute b (M i j))
    (hN : ∀ i j, Commute b (N i j)) (i j : Fin 2) : Commute b ((M * N) i j) := by
  rw [Matrix.mul_apply]
  exact Commute.sum_right _ _ _ fun m _ => (hM i m).mul_right (hN m j)
end Formalism.FourierDecayAlt.P.Wd7
