-- Prove2me | solution 1 for AvramDividend.Classical.firstUpcrossing_prethreshold_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:07:54.154979+00:00
-- url     : https://prove2.me/submissions/273dcad3-b801-4293-aeba-67d7a333374f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞))) :
    ∀ t : ℝ≥0, t < u → X.X t ω ≤ b := by
  intro t ht
  by_contra h
  have hgt : b < X.X t ω := lt_of_not_ge h
  have hle :
      (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞)) ≤
        (t : ℝ≥0∞) := by
    exact iInf_le_of_le t
      (iInf_le (fun _ : b < X.X t ω => (t : ℝ≥0∞)) hgt)
  rw [← hu] at hle
  have hlt : (t : ℝ≥0∞) < (u : ℝ≥0∞) :=
    (ENNReal.coe_lt_coe).mpr ht
  exact (not_le_of_gt hlt) hle
