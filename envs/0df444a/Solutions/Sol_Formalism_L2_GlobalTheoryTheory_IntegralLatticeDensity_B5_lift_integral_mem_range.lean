-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.lift_integral_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:12:01.441124+00:00
-- url     : https://prove2.me/submissions/3ebf858d-3bc2-4a3b-8baa-b230c4f6d3c0

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_LineR
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_SumEmbDualBasisComplex
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_FractionalIdealDualFamily
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_coe_lift_intermediate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open NumberField Classical
open scoped Pointwise
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
theorem _root_.solution (M : IntermediateField ℚ ℂ) [NumberField M] {z : ℂ} (hz : z ∈ M)
    (hi : IsIntegral ℤ z) : liftM M z ∈ (algebraMap (𝓞 M) M).range := by
  have hint : IsIntegral ℤ (liftM M z) := by
    rw [← isIntegral_algHom_iff ((IntermediateField.val M).restrictScalars ℤ) Subtype.val_injective]
    have h1 : ((IntermediateField.val M).restrictScalars ℤ) (liftM M z) = z := coe_lift_intermediate hz
    rw [h1]
    exact hi
  exact ⟨⟨liftM M z, hint⟩, rfl⟩
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
