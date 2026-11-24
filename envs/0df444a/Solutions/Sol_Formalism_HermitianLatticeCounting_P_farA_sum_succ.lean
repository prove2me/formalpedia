-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.farA_sum_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:41.334742+00:00
-- url     : https://prove2.me/submissions/f866f01d-164d-4c58-9001-652e5009f66a

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_farA_succ_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {B h ε : ℝ} (hε : 0 < ε) (h32 : 32 * B ≤ h * ε) (h16 : 16 ≤ h * ε ^ 2) (m : ℕ) :
    ∑ k ∈ range m, farA B h ε (k+1) ≤ 2 * Real.exp (-(h * ε ^ 2 / 16)) := by
  calc ∑ k ∈ range m, farA B h ε (k+1)
      ≤ ∑ k ∈ range m, Real.exp (-(h * ε ^ 2 / 16)) * (1 / 2) ^ k :=
        Finset.sum_le_sum fun k _ => farA_succ_le hε h32 h16 k
    _ = Real.exp (-(h * ε ^ 2 / 16)) * ∑ k ∈ range m, (1 / 2 : ℝ) ^ k := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-(h * ε ^ 2 / 16)) * 2 := by
        gcongr
        exact sum_geometric_two_le m
    _ = _ := by ring
end Formalism.HermitianLatticeCounting.P
