-- Prove2me | solution 5 for AvramDividend.Classical.scaleFunction_excursion_tail_derivative_representation_of_infinite_small_jump
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T09:15:20.536376+00:00
-- url     : https://prove2.me/submissions/12dd5c5a-a281-4e2f-a244-7965446195fb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_excursion_integrated_scale_representation
import Theorems.Thm_AvramDividend_Classical_excursion_integral_scale_derivative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

-- Excursion-tail derivative via authoritative child 49ac + Proved derivative bridge.
-- Route: hvar (integral = top) implies not BoundedVariation; Open 49acdc06 gives
-- phi/mu with continuous tail and W interval-exp; Proved 5b518605 gives HasDerivAt,
-- hence DifferentiableAt and deriv identity. First attempt on UNATTEMPTED 55c2640d.
-- Expect SKETCH while 49acdc06 is Open. No local Lean was run.
-- ProofCheckpoint: MATHEMATICAL_DECOMPOSITION.
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
        {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
        (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
        (q : ℝ) (hq : 0 < q)
        (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) = ⊤) :
    ∃ (φ : ℝ) (μ : Measure ℝ),
      0 < φ ∧ NullSingletonClass μ ∧
      (∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤) ∧
      (∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x) ∧
      (∀ x : ℝ, 0 < x →
        deriv W x = W x * (φ + μ.real (Ici x))) := by
  have hnbv : ¬ X.BoundedVariation := by
    intro hBV
    have hfin : (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) < ⊤ :=
      hBV.2
    rw [hvar] at hfin
    exact lt_irrefl ⊤ hfin
  obtain ⟨φ, μ, hφ, hNull, hfin, hcont, hexp⟩ :=
    AvramDividend.Classical.unbounded_esscher_excursion_integrated_scale_representation
      X q hq W hW hnbv
  have hHas : ∀ x : ℝ, 0 < x →
      HasDerivAt W (W x * (φ + μ.real (Ici x))) x :=
    AvramDividend.Classical.excursion_integral_scale_derivative
      W φ μ hcont hexp
  refine ⟨φ, μ, hφ, hNull, hfin, ?_, ?_⟩
  · intro x hx
    exact (hHas x hx).differentiableAt
  · intro x hx
    exact (hHas x hx).deriv
