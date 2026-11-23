-- Prove2me | solution 1 for Formalism.DivisionValues.W5.tele
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:24:07.504739+00:00
-- url     : https://prove2.me/submissions/2b3a0a46-73d7-4dce-bcb9-043c2f60bd38

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_UntwistedChoice
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_PlaceSumSquares
import Theorems.Thm_Formalism_DivisionValues_W5_log_le_near

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.W5
namespace Formalism.DivisionValues.W5
theorem _root_.solution (u h : ℝ) (hh : 0 < h) (hu : 2 * h ≤ u) (hlog : 2 ≤ Real.log u) :
    h * (Real.log u / u ^ 2) ≤ (Real.log (u - h) + 1) / (u - h) - (Real.log u + 1) / u := by
  obtain ⟨v, hv⟩ : ∃ v, v = u - h := ⟨_, rfl⟩
  have hu' : u = v + h := by linarith
  have hv0 : 0 < v := by linarith
  have hu0 : 0 < u := by linarith
  rw [← hv]
  have h1 := log_le_near u v hu0 hv0
  have h2 : Real.log u - h / v ≤ Real.log v := by
    have : (u - v) / v = h / v := by rw [hu']; ring
    linarith
  set ℓ := Real.log u with hℓ
  have h3 : (ℓ - h / v + 1) / v ≤ (Real.log v + 1) / v :=
    div_le_div_of_nonneg_right (by linarith) hv0.le
  have h4 : (ℓ - h / v + 1) / v - (ℓ + 1) / u - h * (ℓ / u ^ 2) =
      h ^ 2 * (ℓ * v - u) / (u ^ 2 * v ^ 2) := by
    rw [hu']
    field_simp
    ring
  have h5 : 0 ≤ h ^ 2 * (ℓ * v - u) / (u ^ 2 * v ^ 2) := by
    apply div_nonneg _ (by positivity)
    apply mul_nonneg (by positivity)
    nlinarith
  linarith
end Formalism.DivisionValues.W5
