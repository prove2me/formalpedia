-- Prove2me | solution 2 for AvramDividend.Classical.unbounded_unstopped_scale_not_martingale_of_upward_probability
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:24:12.029614+00:00
-- url     : https://prove2.me/submissions/3893f5ed-802e-4d95-9322-98b3c3385be4

import Theorems.Thm_AvramDividend_Classical_unbounded_unstopped_scale_martingale_forces_nonpositive_paths
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.Probability.Martingale.Basic

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal
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
  obtain ⟨t, ht⟩ := hUp
  have h := AvramDividend.Classical.unbounded_unstopped_scale_martingale_forces_nonpositive_paths
    X q W hW hnbv hW0 hStart hMart t
  rw [ae_iff] at h
  have e : {ω : Ω | ¬ X.X t ω ≤ 0} = {ω : Ω | 0 < X.X t ω} := by ext ω; simp
  rw [e] at h
  exact absurd h ht.ne' 
