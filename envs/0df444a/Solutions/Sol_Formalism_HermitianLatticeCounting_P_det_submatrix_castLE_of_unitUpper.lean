-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.det_submatrix_castLE_of_unitUpper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:33.772963+00:00
-- url     : https://prove2.me/submissions/a5afdfd8-a347-4f19-90b9-e4812ee897f3

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_DetMulEqSumProdMulDetSubmatrix

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
theorem _root_.solution {R : Type*} [CommRing R] {N l : ℕ} (hl : l ≤ N)
    (Up : Matrix (Fin N) (Fin N) R) (h1 : ∀ i, Up i i = 1) (h0 : ∀ i j, j < i → Up i j = 0) :
    (Up.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp [h1]
  · intro i j hij
    exact h0 _ _ (by simpa using hij)
end Formalism.HermitianLatticeCounting.P
