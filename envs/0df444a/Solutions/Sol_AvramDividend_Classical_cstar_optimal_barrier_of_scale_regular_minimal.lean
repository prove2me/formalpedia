-- Prove2me | solution 1 for AvramDividend.Classical.cstar_optimal_barrier_of_scale_regular_minimal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T12:58:41.369901+00:00
-- url     : https://prove2.me/submissions/7a636a55-7850-4921-bf34-d5415b98683c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_optimal_barrier_of_regular_minimal

open AvramDividend.Classical
open MeasureTheory Set
open scoped ENNReal NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hfinite : cstar W < ⊤)
    (hshape : ((cstar W).toReal = 0 ∧ W 0 = 0) ∨
      ∃ d : ℝ, 0 < d ∧
        scaleDeriv W (cstar W).toReal = (d : EReal) ∧
        (∀ a : ℝ, 0 ≤ a →
          scaleDeriv W a = ⊤ ∨
            (scaleDeriv W a).toReal = 0 ∨
            d ≤ (scaleDeriv W a).toReal) ∧
        DifferentiableOn ℝ W (Set.Ioo 0 (cstar W).toReal) ∧
        (∀ t ∈ Set.Ioo 0 (cstar W).toReal, d ≤ deriv W t)) :
    cstar W < ⊤ ∧
      ∀ x a : ℝ, 0 ≤ x → x ≤ (cstar W).toReal → 0 ≤ a →
        barrierValue W a x ≤ vcstar W x := by
  have hnonneg : ∀ y : ℝ, 0 ≤ y → 0 ≤ W y := hW.2.1
  have hcont : ContinuousOn W (Set.Icc 0 (cstar W).toReal) := by
    apply hW.2.2.1.mono
    intro x hx
    simpa only [Set.mem_Ici] using hx.1
  apply cstar_optimal_barrier_of_regular_minimal W hfinite hnonneg
  rcases hshape with hz | ⟨d, hd, hc, hden, hdiff, hder⟩
  · exact Or.inl hz
  · exact Or.inr ⟨d, hd, hc, hden, hcont, hdiff, hder⟩
