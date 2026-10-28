-- Prove2me | solution 2 for AvramDividend.Classical.unbounded_discounted_scale_unstopped_martingale_impossible
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:31:41.069843+00:00
-- url     : https://prove2.me/submissions/967fc536-840b-48e0-b669-2e9587e28335

import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_chat04_psi_eventually_gt_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_unstopped_scale_martingale_forces_nonpositive_paths
import Theorems.Thm_AvramDividend_Classical_positive_psi_excludes_nonpositive_one_increment_ae
import Mathlib.Probability.Martingale.Basic

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    [SigmaFiniteFiltration P 𝓕]
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    ¬ Martingale
      (fun t : ℝ≥0 => fun ω : Ω =>
        Real.exp (-(q * (t : ℝ))) * W (X.X t ω)) 𝓕 P := by
  intro hMart
  have hW0 := AvramDividend.Classical.chat04_scale_zero_origin_of_unbounded_variation X hnbv q hq W hW
  have hnp := AvramDividend.Classical.unbounded_unstopped_scale_martingale_forces_nonpositive_paths X q W hW hnbv
    hW0 (Filter.Eventually.of_forall fun ω => X.X_zero ω) hMart 1
  obtain ⟨β₀, hβ₀, hgt⟩ := AvramDividend.Classical.chat04_psi_eventually_gt_of_unbounded_variation X q hq hnbv
  exact AvramDividend.Classical.positive_psi_excludes_nonpositive_one_increment_ae X β₀ hβ₀
    (lt_trans hq (hgt β₀ le_rfl)) hnp
