-- Prove2me | solution 1 for AvramDividend.Classical.chat07_bv_cap_generator_harmonic_of_laplace_family
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T18:17:25.353135+00:00
-- url     : https://prove2.me/submissions/80a4f43e-2c2f-47ef-9fd0-9c003e185ab9

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat07_bv_c2_generator_harmonic_of_full_laplace_family
import Theorems.Thm_AvramDividend_Classical_chat07_bv_cap_harmonic_from_regular_scale_and_interior

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! Full-family residual transforms imply exact generator identity at the BV dividend cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hbv : X.BoundedVariation) (hσ : X.σ = 0)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (ha : 0 < (cstar W).toReal)
    (hWdiff : DifferentiableAt ℝ W (cstar W).toReal)
    (hWderiv : deriv W (cstar W).toReal ≠ 0)
    (hC1 : ContDiffOn ℝ 1 W (Ioi 0))
    (hC2 : ContDiffOn ℝ 2 W (Ioi 0))
    (hweighted : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) = 0) :
    X.GeneratorIntegrable (vcstar W) (cstar W).toReal ∧
      X.generator (vcstar W) (cstar W).toReal -
        q * vcstar W (cstar W).toReal = 0 := by
  have hinside : ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.generator W x - q * W x = 0 := by
    intro x hx
    exact (chat07_bv_c2_generator_harmonic_of_full_laplace_family
      X hX hbv q hq W hW (cstar W).toReal ha hC1 hC2 hweighted
      x hx).2
  exact chat07_bv_cap_harmonic_from_regular_scale_and_interior
    X hX hbv hσ q W hW ha hWdiff hWderiv hC1 hC2 hinside
