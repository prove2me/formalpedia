-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.assembly_of_second_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:40.803211+00:00
-- url     : https://prove2.me/submissions/06d3a3da-f994-4896-84f3-006f732be7a1

import Definitions.Def_Formalism_FlagUnipotentLattices_MemLpTwoOfOneTop
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_InterlacingOfBlocksSecondCase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S8 MeasureTheory Filter Topology TensorProduct Finset
set_option linter.all false
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : AssemblyB := by
  intro T _ μ E _ _ P χ W h1 h2 h0
  have e1 : (∫ x, (inner ℂ (W x) (P (fun y => (χ y : ℂ) • W y) x) : ℂ) ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [h0] with x hx
    simp only [hx, Pi.zero_apply, inner_zero_right]
  have e2 : (∫ x, (inner ℂ (W x) ((χ x : ℂ) • W x) : ℂ) ∂μ) = ((∫ x, χ x * ‖W x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1; ext x
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [e1, e2] at h1
  have := Complex.ofReal_eq_zero.mp h1.symm
  linarith
end Formalism.HermitianLatticeCounting.P
