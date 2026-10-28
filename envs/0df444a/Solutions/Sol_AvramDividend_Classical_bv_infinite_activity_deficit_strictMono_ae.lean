-- Prove2me | solution 1 for AvramDividend.Classical.bv_infinite_activity_deficit_strictMono_ae
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:07:47.318485+00:00
-- url     : https://prove2.me/submissions/4f609f3a-8ac1-4492-bec1-634429b5329c

import Theorems.Thm_AvramDividend_Classical_bv_infinite_activity_deficit_strictMono_of_dense_grid
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.NNReal.Lemmas

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hνinf : X.ν (Iio (0 : ℝ)) = ⊤) :
    ∀ᵐ ω ∂P, StrictMono
      (fun t : ℝ≥0 => X.drift * (t : ℝ) - X.X t ω) := by
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq ℝ≥0
  exact bv_infinite_activity_deficit_strictMono_of_dense_grid X hBV hνinf u hu
