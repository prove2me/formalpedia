-- Prove2me | solution 1 for Eden.exteriorBasis_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:08:59.963869+00:00
-- url     : https://prove2.me/submissions/7cf3dc16-c685-4be3-8f7d-453b59a14ebb

import Definitions.Def_Eden_DerivativeDecomposition
import Mathlib.Analysis.InnerProductSpace.ExteriorPower
import Definitions.Def_Eden_ExteriorGeometry

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (k : ℕ) (s : ExteriorIndex k) :
    exteriorBasis k s = exteriorPower.ιMulti_family ℝ k
      (EuclideanSpace.basisFun (Fin 5) ℝ) s := by
  change ((EuclideanSpace.basisFun (Fin 5) ℝ).exteriorPower k).toBasis s = _
  rw [OrthonormalBasis.toBasis_exteriorPower, exteriorPower.basis_apply]
  rfl
end Eden
