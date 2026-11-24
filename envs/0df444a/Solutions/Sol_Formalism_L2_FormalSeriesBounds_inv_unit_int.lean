-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.inv_unit_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:10:28.409506+00:00
-- url     : https://prove2.me/submissions/7d98ae17-7acc-496f-b389-fc00dd10ec76

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {a : C} (h : V.v a = 0) : V.Ge 0 a⁻¹ := by
  have ha : a ≠ 0 := by
    rintro rfl
    rw [AddValuation.map_zero] at h
    exact WithTop.top_ne_zero h
  have e : V.v a + V.v a⁻¹ = 0 := by
    rw [← AddValuation.map_mul, mul_inv_cancel₀ ha, AddValuation.map_one]
  rw [h, zero_add] at e
  show ((0 : ℝ) : WithTop ℝ) ≤ V.v a⁻¹
  rw [e, WithTop.coe_zero]
end Formalism.L2.FormalSeriesBounds
