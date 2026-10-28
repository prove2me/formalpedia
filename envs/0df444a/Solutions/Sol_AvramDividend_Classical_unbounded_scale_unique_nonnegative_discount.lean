-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_unique_nonnegative_discount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:14:11.038993+00:00
-- url     : https://prove2.me/submissions/b6c441ad-2f9a-49ee-93ba-f8c8bb9a0bbe

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_psi_two_discounts_common_tail
import Theorems.Thm_AvramDividend_Classical_continuousOn_Ioi_eq_of_laplace_eq_signed
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Defs.Filter
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Scale functions of the same nonnegative discount agree on positive reserves. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q)
    (W₁ W₂ : ℝ → ℝ)
    (hW₁ : IsScaleFunction X q W₁)
    (hW₂ : IsScaleFunction X q W₂) :
    ∀ x : ℝ, 0 < x → W₁ x = W₂ x := by
  obtain ⟨b, hb, hlarge⟩ :=
    unbounded_psi_two_discounts_common_tail X hnbv q q hq hq
  have hC₁ : ContinuousOn W₁ (Ioi (0 : ℝ)) :=
    hW₁.2.2.1.mono (by intro x hx; exact le_of_lt (Set.mem_Ioi.mp hx))
  have hC₂ : ContinuousOn W₂ (Ioi (0 : ℝ)) :=
    hW₂.2.2.1.mono (by intro x hx; exact le_of_lt (Set.mem_Ioi.mp hx))
  apply continuousOn_Ioi_eq_of_laplace_eq_signed W₁ W₂ b hC₁ hC₂
  intro θ hθ
  obtain ⟨hθnonneg, hψ₁, _⟩ := hlarge θ hθ
  obtain ⟨hI₁, hLap₁⟩ := hW₁.2.2.2.2 θ hθnonneg hψ₁
  obtain ⟨hI₂, hLap₂⟩ := hW₂.2.2.2.2 θ hθnonneg hψ₁
  refine ⟨?_, ?_, ?_⟩
  · simpa only [neg_mul] using hI₁
  · simpa only [neg_mul] using hI₂
  · simpa only [neg_mul] using hLap₁.trans hLap₂.symm
