-- Prove2me | solution 3 for AvramDividend.Classical.bv_infinite_activity_deficit_strictMono_of_dense_grid
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:57:22.160053+00:00
-- url     : https://prove2.me/submissions/ef1a1b9a-2e70-45db-8d03-e7a05407cf6a

import Theorems.Thm_AvramDividend_Classical_bv_infinite_activity_deficit_strict_grid_pairs
import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.MeasureTheory.OuterMeasure.AE

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hνinf : X.ν (Iio (0 : ℝ)) = ⊤)
    (grid : ℕ → ℝ≥0) (hDense : DenseRange grid) :
    ∀ᵐ ω ∂P, StrictMono
      (fun t : ℝ≥0 => X.drift * (t : ℝ) - X.X t ω) := by
  filter_upwards [bv_infinite_activity_deficit_strict_grid_pairs X hBV hνinf grid,
    bv_drift_deficit_ae_monotone_all_times X hBV] with ω hp hm
  intro s t hst
  obtain ⟨_, ⟨i, rfl⟩, hsi, hit⟩ := hDense.exists_between hst
  obtain ⟨_, ⟨j, rfl⟩, hij, hjt⟩ := hDense.exists_between hit
  exact lt_of_le_of_lt (hm hsi.le) (lt_of_lt_of_le (hp i j hij) (hm hjt.le))
