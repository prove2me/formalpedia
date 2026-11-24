-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd8.cw_mat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:15.007834+00:00
-- url     : https://prove2.me/submissions/cce85fbf-5f46-46b4-92e9-332e4af2e826

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd8
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd8
theorem _root_.solution (X X' Q V VH U : M2 (SlopeTestRemainingChoices S A)) (hA : X' * V * U = U * V * X')
    (hB : VH * X * U = U * X * VH) (hQ : Commute Q U) :
    VH * (X * Q * X') * V * U = U * X * (VH * Q * V) * X' := by
  calc VH * (X * Q * X') * V * U = VH * X * Q * (X' * V * U) := by simp only [mul_assoc]
    _ = VH * X * Q * (U * V * X') := by rw [hA]
    _ = VH * X * (Q * U) * V * X' := by simp only [mul_assoc]
    _ = VH * X * (U * Q) * V * X' := by rw [hQ.eq]
    _ = VH * X * U * Q * V * X' := by simp only [mul_assoc]
    _ = U * X * VH * Q * V * X' := by rw [hB]
    _ = U * X * (VH * Q * V) * X' := by simp only [mul_assoc]
end Formalism.FourierDecayAlt.P.Wd8
