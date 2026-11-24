-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.leadingMinorTriangularInvariant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:27.537475+00:00
-- url     : https://prove2.me/submissions/c6da165a-22b4-4d43-bfc7-d406738cc023

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_DetMulEqSumProdMulDetSubmatrix
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_submatrix_mul_castLE_of_lower
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_submatrix_mul_castLE_of_upper
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_det_submatrix_castLE_of_unitLower
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_det_submatrix_castLE_of_unitUpper

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
theorem _root_.solution : LeadingMinorInvariant := by
  intro R _ N l hl Lo W Up hL1 hL0 hU1 hU0
  rw [Matrix.mul_assoc, submatrix_mul_castLE_of_lower hl Lo (W * Up) _ (fun i j hi hj => hL0 i j (by
      rw [Fin.lt_def]; omega)),
    submatrix_mul_castLE_of_upper hl W Up _ (fun i j hi hj => hU0 i j (by rw [Fin.lt_def]; omega)),
    Matrix.det_mul, Matrix.det_mul, det_submatrix_castLE_of_unitLower hl Lo hL1 hL0, det_submatrix_castLE_of_unitUpper hl Up hU1 hU0]
  ring
end Formalism.HermitianLatticeCounting.P
