-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_original_rightcont_finite_simple_rectangles
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:03:10.704272+00:00
-- url     : https://prove2.me/submissions/0cacc05e-47df-4a26-8eac-362796cbf0c4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_rightcont_stopped_future_rect

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Finite nonnegative predictable simple rectangles have their original stopped mean. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω = ((Measure.count.restrict
      {u : ℝ≥0 | 0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hK : ∀ ω, K ω = @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
      (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))
      (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω))
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμclock : ∀ E : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] E →
      μ E = ((((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) E)
    (N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hN : N = (letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable;
      μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
    {ι : Type*} (S : Finset ι)
    (i : ι → ℝ≥0) (A : ι → Set Ω)
    (hA : ∀ k ∈ S, MeasurableSet[𝓕.rightCont (i k)] (A k))
    (B : ι → Set ℝ) (hB : ∀ k ∈ S, MeasurableSet (B k))
    (w : ι → ℝ≥0∞) :
    (∑ k ∈ S, w k *
      (M.restrict {p | p.1.1 ≤ T})
        ((Ioi (i k) ×ˢ A k) ×ˢ B k)) =
      ∑ k ∈ S, w k * N ((Ioi (i k) ×ˢ A k) ×ˢ B k) := by
  classical
  apply Finset.sum_congr rfl
  intro k hk
  rw [avram_p2_e_compensator_original_rightcont_stopped_future_rect
    X T NX hNX K hK M hM μ hμclock N hN (i k) (A k)
    (hA k hk) (B k) (hB k hk)]
