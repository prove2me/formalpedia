-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G2.det_blk_col_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:11.054069+00:00
-- url     : https://prove2.me/submissions/f77c3af0-e48e-4153-86dc-9bd25cc50352

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
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (a : Fin n → ℂ) (e : ℂ) :
    (blk A 0 a e).det = A.det * e := by
  unfold blk
  rw [Matrix.det_reindex_self]
  have h : (Matrix.of fun i (_ : Fin 1) => (0 : Fin n → ℂ) i) = (0 : Matrix (Fin n) (Fin 1) ℂ) := by
    ext i j; simp
  rw [h, Matrix.det_fromBlocks_zero₁₂]
  simp
end Formalism.FourierDecayAlt.P.G2
