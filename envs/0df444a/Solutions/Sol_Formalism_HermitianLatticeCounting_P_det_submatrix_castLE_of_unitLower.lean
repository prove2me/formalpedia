-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.det_submatrix_castLE_of_unitLower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:37.985918+00:00
-- url     : https://prove2.me/submissions/a2fada46-82b5-4d38-a7bb-15db937595e7

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
    (Lo : Matrix (Fin N) (Fin N) R) (h1 : ∀ i, Lo i i = 1) (h0 : ∀ i j, i < j → Lo i j = 0) :
    (Lo.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [h1]
  · intro i j hij
    exact h0 _ _ (by simpa using hij)
end Formalism.HermitianLatticeCounting.P
