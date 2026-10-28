-- Prove2me | solution 1 for AvramDividend.Classical.bv_infinite_activity_deficit_strictMono_of_dense_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:55:54.575685+00:00
-- url     : https://prove2.me/submissions/c6115bc3-a033-4a5e-8c5d-83cd6a41481d

import Theorems.Thm_AvramDividend_Classical_bv_infinite_activity_deficit_strict_grid_pairs
import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

/-- Strict increase on a dense countable grid and monotonicity imply strictly increasing deficit paths. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hνinf : X.ν (Iio (0 : ℝ)) = ⊤)
    (grid : ℕ → ℝ≥0) (hDense : DenseRange grid) :
    ∀ᵐ ω ∂P, StrictMono
      (fun t : ℝ≥0 => X.drift * (t : ℝ) - X.X t ω) := by
  filter_upwards
    [bv_infinite_activity_deficit_strict_grid_pairs X hBV hνinf grid,
      bv_drift_deficit_ae_monotone_all_times X hBV]
    with ω hPairs hMono
  intro s t hst
  obtain ⟨m, hsm, hmt⟩ := exists_between hst
  obtain ⟨u, hsu, hum⟩ := exists_between hsm
  obtain ⟨v, hmv, hvt⟩ := exists_between hmt
  obtain ⟨i, hi⟩ :=
    hDense.exists_mem_open isOpen_Ioo ⟨u, hsu, hum⟩
  obtain ⟨j, hj⟩ :=
    hDense.exists_mem_open isOpen_Ioo ⟨v, hmv, hvt⟩
  have hij : grid i < grid j := hi.2.trans hj.1
  calc
    X.drift * (s : ℝ) - X.X s ω ≤
        X.drift * (grid i : ℝ) - X.X (grid i) ω :=
      hMono hi.1.le
    _ < X.drift * (grid j : ℝ) - X.X (grid j) ω :=
      hPairs i j hij
    _ ≤ X.drift * (t : ℝ) - X.X t ω :=
      hMono hj.2.le
