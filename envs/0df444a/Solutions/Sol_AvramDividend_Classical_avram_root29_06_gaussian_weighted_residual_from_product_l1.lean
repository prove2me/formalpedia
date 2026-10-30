-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_06_gaussian_weighted_residual_from_product_l1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T11:33:39.02082+00:00
-- url     : https://prove2.me/submissions/20ffc056-2e8d-4d78-9525-ef305a5cc77d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_root29_06_gaussian_residual_family
import Theorems.Thm_AvramDividend_Classical_bv_weighted_jump_integrable_of_product_integrable
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_weighted_global_fubini_of_prod_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Product L1 simultaneously supplies the jump integral and the Fubini exchange. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hσ : 0 < X.σ)
    (hD2 : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ =>
        Real.exp (-(θ * x)) * deriv (deriv W) x) (Ioi (0 : ℝ)))
    (hprod : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      Integrable (fun p : ℝ × ℝ =>
        Real.exp (-(θ * p.1)) *
          SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (X.ν.restrict (Iio (0 : ℝ))))) :
    ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ =>
        Real.exp (-(θ * x)) * (X.generator W x - q * W x))
        (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) * (X.generator W x - q * W x)) = 0 := by
  apply avram_root29_06_gaussian_residual_family
    X hX q hq W hW hσ hD2
  · intro θ hθ hqθ
    exact bv_weighted_jump_integrable_of_product_integrable
      X θ W (hprod θ hθ hqθ)
  · intro θ hθ hqθ
    exact scaleFunction_generator_weighted_global_fubini_of_prod_integrable
      X W θ (hprod θ hθ hqθ)
