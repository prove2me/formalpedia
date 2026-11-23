-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G2.det_wMat_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:40:08.761796+00:00
-- url     : https://prove2.me/submissions/62d595c6-4b34-4e26-9dfd-5c0f155778b2

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G2
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.G2
theorem _root_.solution (n : ℕ) : (wMat (n + 1)).det = (-1) ^ n * (wMat n).det := by
  rw [Matrix.det_succ_row_zero]
  rw [Finset.sum_eq_single (Fin.last n)]
  · have h : (wMat (n + 1)).submatrix Fin.succ (Fin.last n).succAbove = wMat n := by
      ext i j
      simp [wMat, Fin.rev_succ]
    rw [h]
    simp [wMat]
  · intro j _ hj
    simp [wMat, hj]
  · simp
end Formalism.FourierDecayAlt.P.G2
