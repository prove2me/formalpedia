-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.det_gramSchmidt_coeff_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:33.793412+00:00
-- url     : https://prove2.me/submissions/32d71205-ff90-44b8-be1f-6b927636cb7a

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SchurAverage

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
open InnerProductSpace
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {r : ℕ} (a : Fin r → U) : (s5bL a).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [s5bL]
  · intro i j hij
    have h : i < j := by simpa using hij
    simp [s5bL, not_lt.2 h.le, h.ne']
end Formalism.HermitianLatticeCounting.P
