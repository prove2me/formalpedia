-- Prove2me | solution 2 for AvramDividend.Classical.bv_infinite_activity_deficit_strictMono_of_dense_grid
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:56:38.095516+00:00
-- url     : https://prove2.me/submissions/9d771348-da79-4a8e-bd8c-325bd1d1f915

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
    bv_drift_deficit_ae_monotone_all_times X hBV] with ω hp hm s t hst
  obtain ⟨i, hi⟩ := hDense.exists_mem_open isOpen_Ioo (nonempty_Ioo.2 hst)
  obtain ⟨j, hj⟩ := hDense.exists_mem_open isOpen_Ioo (nonempty_Ioo.2 hi.2)
  calc X.drift * (s : ℝ) - X.X s ω ≤ X.drift * (grid i : ℝ) - X.X (grid i) ω := hm hi.1.le
    _ < X.drift * (grid j : ℝ) - X.X (grid j) ω := hp i j hj.1
    _ ≤ X.drift * (t : ℝ) - X.X t ω := hm hj.2.le
