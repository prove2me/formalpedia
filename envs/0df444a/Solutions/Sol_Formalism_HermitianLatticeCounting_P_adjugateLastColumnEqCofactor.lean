-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.adjugateLastColumnEqCofactor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:40.518845+00:00
-- url     : https://prove2.me/submissions/2942ab4d-7cac-4c0f-bda4-392fafdbf8fd

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : CofVecAdjugate := by
  intro R _ r Z b
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.cofVec
  rw [Fin.val_last, pow_add]
  simp only [Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp]
  ring
end Formalism.HermitianLatticeCounting.P
