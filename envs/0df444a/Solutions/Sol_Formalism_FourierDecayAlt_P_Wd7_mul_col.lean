-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd7.mul_col
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:06.15845+00:00
-- url     : https://prove2.me/submissions/4baba550-64b6-4462-842b-beb2501edf2d

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
theorem _root_.solution (M N : M2 (SlopeTestRemainingChoices S A))
    (hN : ∀ (m : Fin 2) (z : Ix S), (N m 0) z e1 = if m = 0 ∧ z = e1 then 1 else 0)
    (k : Fin 2) (z : Ix S) : ((M * N) k 0) z e1 = (M k 0) z e1 := by
  rw [Matrix.mul_apply, Matrix.sum_apply]
  simp only [Matrix.mul_apply, hN]
  rw [Fin.sum_univ_two]
  simp
end Formalism.FourierDecayAlt.P.Wd7
