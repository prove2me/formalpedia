-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s5b7_unit_ball
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:26.686836+00:00
-- url     : https://prove2.me/submissions/f643c770-b288-454c-a274-25996f11d2ec

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MeasurePreservingPiCompProd
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5b7_finrank_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Module Matrix MeasureTheory Set
open scoped BigOperators ComplexConjugate
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (d : ℕ) :
    (volume : Measure (EuclideanSpace ℂ (Fin (d + 1)))).real (Metric.ball 0 1) =
      Real.pi ^ (d + 1) / ((d + 1).factorial : ℝ) := by
  rw [Measure.real, InnerProductSpace.volume_ball, s5b7_finrank_real]
  have h1 : Real.sqrt Real.pi ^ (2 * (d + 1)) = Real.pi ^ (d + 1) := by
    rw [pow_mul, Real.sq_sqrt Real.pi_pos.le]
  have h2 : Real.Gamma (((2 * (d + 1) : ℕ) : ℝ) / 2 + 1) = ((d + 1).factorial : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial]
    congr 1
    push_cast
    ring
  rw [h1, h2]
  simp only [ENNReal.ofReal_one, one_pow, one_mul]
  exact ENNReal.toReal_ofReal (by positivity)
end Formalism.HermitianLatticeCounting.P
