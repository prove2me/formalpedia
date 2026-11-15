-- Prove2me | solution 1 for AvramDividend.Classical.avram_a61_independent_real_product_integrability_and_mean_factorization_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:27:49.652609+00:00
-- url     : https://prove2.me/submissions/301c2496-8e5e-403a-9f00-cdf08dbd811c

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

/-- Independent nonzero real factors: integrability of the product implies integrability of the left factor and exact mean factorisation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (F J : Ω → ℝ)
    (hMF : Measurable F) (hMJ : Measurable J)
    (hInd : F ⟂ᵢ[P] J)
    (hProd : Integrable (fun ω => F ω * J ω) P)
    (hNonzero : ¬ (J =ᵐ[P] fun _ => (0 : ℝ))) :
    Integrable F P ∧
      (∫ ω, F ω * J ω ∂P) =
        (∫ ω, F ω ∂P) * (∫ ω, J ω ∂P) := by
  have hB : ∀ x y : ℝ,
      (1 : ℝ≥0) * ‖x‖ₑ * ‖y‖ₑ ≤ ‖x * y‖ₑ := by
    intro x y
    simp [enorm_mul]
  have hIntF : Integrable F P :=
    hInd.integrable_left_of_integrable_op
      (fun x y : ℝ => x * y) 1 (by norm_num) hB
      hProd hMF.aestronglyMeasurable hMJ.aestronglyMeasurable hNonzero
  exact ⟨hIntF,
    hInd.integral_mul_eq_mul_integral
      hMF.aestronglyMeasurable hMJ.aestronglyMeasurable⟩
