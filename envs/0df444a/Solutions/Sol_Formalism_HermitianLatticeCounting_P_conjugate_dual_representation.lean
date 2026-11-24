-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.conjugate_dual_representation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:44:19.221183+00:00
-- url     : https://prove2.me/submissions/2b9e2150-98e1-421a-979c-918ca5b849e0

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
theorem _root_.solution : ConjDual := by
  intro E _ _ _ G _ ρ hu g v
  have h1 : ρ g * star (ρ g) = 1 := (Unitary.mem_iff.mp (hu g)).2
  have h2 : ρ g⁻¹ * ρ g = 1 := by rw [← map_mul]; simp
  have h3 : ρ g⁻¹ = star (ρ g) := by
    calc ρ g⁻¹ = ρ g⁻¹ * (ρ g * star (ρ g)) := by rw [h1, mul_one]
      _ = star (ρ g) := by rw [← mul_assoc, h2, one_mul]
  ext y
  simp only [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.comp_apply]
  rw [h3, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
end Formalism.HermitianLatticeCounting.P
