-- Prove2me | solution 1 for Formalism.DivisionValues.reduction_third_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:43.613577+00:00
-- url     : https://prove2.me/submissions/c51d170f-2fe9-4fdf-a68d-99bef8d122ea

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_StatementACE
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionThirdStepMean
import Theorems.Thm_Formalism_DivisionValues_NormSquareReduction_norm_sq_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped InnerProductSpace ComplexConjugate
noncomputable section
open Formalism Formalism.DivisionValues
namespace Formalism.DivisionValues
theorem _root_.solution : StepC := by
  intro Φ Cs Q E _ _ _ _ _ _ _ _ _ ι hsurj Ix _ Qp hsup s smin hsmin hs hι col k hcol P p hP B hB hk hp
    φ e
  obtain ⟨F, rfl⟩ := hsurj e
  have hF := NormSquareReduction.norm_sq_le ι Qp hsup s smin hs hι F
  have hsq : 0 < Real.sqrt smin := Real.sqrt_pos.mpr hsmin
  have hFle : ‖F‖ ≤ ‖ι F‖ / Real.sqrt smin := by
    rw [le_div_iff₀ hsq]
    have h1 : (‖F‖ * Real.sqrt smin) ^ 2 ≤ ‖ι F‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hsmin.le]; linarith
    nlinarith [norm_nonneg (ι F), mul_nonneg (norm_nonneg F) hsq.le]
  rw [hB φ F]
  have h1 := hP (col φ) F
  have h2 := hcol φ
  have hpk : p * ‖col φ‖ * ‖F‖ ≤ p * (k * ‖φ‖) * (‖ι F‖ / Real.sqrt smin) :=
    mul_le_mul (mul_le_mul_of_nonneg_left h2 hp) hFle (norm_nonneg _)
      (mul_nonneg hp (mul_nonneg hk (norm_nonneg _)))
  calc ‖P (col φ) F‖ ≤ p * ‖col φ‖ * ‖F‖ := h1
    _ ≤ p * (k * ‖φ‖) * (‖ι F‖ / Real.sqrt smin) := hpk
    _ = p * k / Real.sqrt smin * ‖φ‖ * ‖ι F‖ := by ring
end Formalism.DivisionValues
