-- Prove2me | solution 1 for AvramDividend.Classical.avram_signed_laplace_ae_zero_of_psi_family_20261026
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:38:38.414798+00:00
-- url     : https://prove2.me/submissions/59cefaa9-d97c-4e71-b02b-0308d99b64f1

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_standing
import Theorems.Thm_AvramDividend_Classical_avram_laplace_ae_zero_of_signed_20261026
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The q-admissible Laplace family contains a uniqueness half-line. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (R : ℝ → ℝ)
    (hlap : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * R x)
        (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * R x) = 0) :
    ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioi (0 : ℝ))), R x = 0 := by
  obtain ⟨β, hβ0, hβ⟩ := psi_eventually_gt_of_standing X hX q hq
  apply avram_laplace_ae_zero_of_signed_20261026 R β
  intro θ hθ
  exact hlap θ (le_trans hβ0 (le_of_lt hθ)) (hβ θ (le_of_lt hθ))
