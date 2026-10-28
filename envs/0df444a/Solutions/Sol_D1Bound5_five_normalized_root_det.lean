-- Prove2me | solution 1 for D1Bound5.five_normalized_root_det
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:24:24.065644+00:00
-- url     : https://prove2.me/submissions/1b393e03-4c6f-403a-9275-0089b6606e6c

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
import Definitions.Def_D1Bound5_DeterminantNormalization_Definitions
import Definitions.Def_D1Bound5_ProductFiveMatrixBridge_Definitions
import Definitions.Def_D1Bound5_ProductFiveRankTwo_Definitions
import Theorems.Thm_D1Bound5_five_integrated_det_of_symmetric_error
import Theorems.Thm_D1Bound5_normalizedRootError_det
import Theorems.Thm_D1Bound5_normalizedRootError_diag

section
open Matrix

namespace D1Bound5













/-- The fully normalized five-entry determinant identity for symmetric
square-root matrices. Only the final tuple element must be nonzero.
The other tuple entries and every off-diagonal square root may vanish. -/
theorem _root_.solution
    (t u : Fin 5 → ℂ) (M : Matrix (Fin 5) (Fin 5) ℂ)
    (hu : ∀ i, (u i)^2 = t i)
    (hdiag : ∀ i, M i i = t i)
    (hsym : Mᵀ = M)
    (hd : fiveLastValue t ≠ 0) :
    (∏ i, t i) * M.det =
      (fiveLastValue t)^2 *
        (productFiveSchur
          (fivePrefixError (normalizedRootError t u M))
          (fiveLastError (normalizedRootError t u M))
          (fivePrefixValues t) (fiveLastValue t)).det := by
  let E := normalizedRootError t u M
  have hEdiag :
      E (Fin.natAdd 4 (0 : Fin 1)) (Fin.natAdd 4 (0 : Fin 1)) = 0 :=
    normalizedRootError_diag t u M hu hdiag _
  have hEsym : Eᵀ = E := by
    ext i j
    change u j * M j i * u i - t j * t i =
      u i * M i j * u j - t i * t j
    have hm := congrArg (fun N : Matrix (Fin 5) (Fin 5) ℂ => N i j) hsym
    change M j i = M i j at hm
    rw [hm]
    ring
  have hp := normalizedRootError_det t u M hu
  exact hp.symm.trans (five_integrated_det_of_symmetric_error t E hEdiag hEsym hd)

end D1Bound5
end
