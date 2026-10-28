-- Prove2me | solution 1 for D1Bound5.five_integrated_det_of_symmetric_error
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:47:24.543995+00:00
-- url     : https://prove2.me/submissions/58fbdb45-ce25-49ec-9db9-e3cf628c63a3

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_ProductFiveBlockDet_Definitions
import Definitions.Def_D1Bound5_ProductFiveMatrixBridge_Definitions
import Definitions.Def_D1Bound5_ProductFiveRankTwo_Definitions
import Theorems.Thm_D1Bound5_five_reindex_rankOne_plus_error
import Theorems.Thm_D1Bound5_productFiveIntegratedBlock_det

section
open Matrix

namespace D1Bound5











/-- The determinant of the actual Fin 5 matrix is the scalar-block
Schur determinant. The equivalence reindexes both rows and columns
simultaneously and therefore introduces no permutation sign. -/
theorem _root_.solution
    (t : Fin 5 → ℂ) (E : Matrix (Fin 5) (Fin 5) ℂ)
    (hdiag : E (Fin.natAdd 4 (0 : Fin 1)) (Fin.natAdd 4 (0 : Fin 1)) = 0)
    (hsym : Eᵀ = E) (hd : fiveLastValue t ≠ 0) :
    (Matrix.of (fun i j => t i * t j + E i j)).det =
      (fiveLastValue t)^2 *
        (productFiveSchur (fivePrefixError E) (fiveLastError E)
          (fivePrefixValues t) (fiveLastValue t)).det := by
  have hm := five_reindex_rankOne_plus_error t E hdiag hsym
  have hdet := congrArg Matrix.det hm
  have hr := Matrix.det_reindex_self
    (finSumFinEquiv : Fin 4 ⊕ Fin 1 ≃ Fin 5).symm
    (Matrix.of (fun i j => t i * t j + E i j))
  exact hr.symm.trans (hdet.trans
    (productFiveIntegratedBlock_det (fivePrefixError E) (fiveLastError E)
      (fivePrefixValues t) (fiveLastValue t) hd))



end D1Bound5
end
