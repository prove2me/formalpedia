-- Prove2me | solution 1 for CMEul.Mult.rpow_le_half
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:51.666943+00:00
-- url     : https://prove2.me/submissions/2ffc4036-8f8a-4df1-b54a-1880260b9515

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_StepRegroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_EulerFactorsMultipliable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open CMEul CMEul.Mult
open Formalism.HermitianLatticesTheory
namespace CMEul.Mult
theorem _root_.solution {x : ℝ} (hx : 2 ≤ x) : x ^ (-(3 / 2 : ℝ)) ≤ 1 / 2 := by
  have h1 : x ^ (-(3 / 2 : ℝ)) ≤ x ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  rw [Real.rpow_neg_one] at h1
  have h2 : x⁻¹ ≤ 1 / 2 := by
    rw [one_div]
    exact inv_anti₀ (by norm_num) hx
  linarith
end CMEul.Mult
