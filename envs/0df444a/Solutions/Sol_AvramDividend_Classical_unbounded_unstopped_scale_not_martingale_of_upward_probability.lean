-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_unstopped_scale_not_martingale_of_upward_probability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T19:23:04.073507+00:00
-- url     : https://prove2.me/submissions/f8dcae90-bb13-4d34-97c7-00c407cfe4be

import Theorems.Thm_AvramDividend_Classical_unbounded_unstopped_scale_martingale_forces_nonpositive_paths
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.Probability.Martingale.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Positive probability of moving above zero contradicts the proposed
un-stopped discounted scale martingale at zero reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    [SigmaFiniteFiltration P 𝓕]
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) (hW0 : W 0 = 0)
    (hStart : ∀ᵐ ω ∂P, X.X 0 ω = 0)
    (hUp : ∃ t : ℝ≥0, 0 < P {ω : Ω | 0 < X.X t ω}) :
    ¬ Martingale
      (fun t : ℝ≥0 => fun ω : Ω =>
        Real.exp (-(q * (t : ℝ))) * W (X.X t ω)) 𝓕 P := by
  intro hMart
  obtain ⟨t, hPositiveEvent⟩ := hUp
  have hnonpos :=
    unbounded_unstopped_scale_martingale_forces_nonpositive_paths
      X q W hW hnbv hW0 hStart hMart t
  have hnull : P {ω : Ω | ¬ X.X t ω ≤ 0} = 0 :=
    (ae_iff).mp hnonpos
  have hset :
      {ω : Ω | 0 < X.X t ω} =
        {ω : Ω | ¬ X.X t ω ≤ 0} := by
    ext ω
    simp only [Set.mem_setOf_eq, not_le]
  rw [hset, hnull] at hPositiveEvent
  exact (lt_irrefl (0 : ℝ≥0∞)) hPositiveEvent
