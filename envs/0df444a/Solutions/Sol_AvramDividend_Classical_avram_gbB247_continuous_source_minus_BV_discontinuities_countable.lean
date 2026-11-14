-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB247_continuous_source_minus_BV_discontinuities_countable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:25:45.649786+00:00
-- url     : https://prove2.me/submissions/11af544c-4976-4e41-929e-402116c6ab64

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB246_locally_BV_time_path_discontinuities_countable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Actual controlled reserve time discontinuities inherit countability from its BV correction. -/
theorem solution
    (f : ℝ≥0 → ℝ) (hf : Continuous f)
    (d : ℝ≥0 → ℝ)
    (hd : LocallyBoundedVariationOn d Set.univ)
    (x : ℝ) :
    Set.Countable {t : ℝ≥0 |
      ¬ ContinuousAt (fun s : ℝ≥0 => x + f s - d s) t} := by
  have hdCount : Set.Countable
      {t : ℝ≥0 | ¬ ContinuousAt d t} :=
    avram_gbB246_locally_BV_time_path_discontinuities_countable d hd
  apply hdCount.mono
  intro t ht
  by_contra hdc
  have hdc' : ContinuousAt d t := by simpa using hdc
  have hfc : ContinuousAt f t := hf.continuousAt
  have hc : ContinuousAt (fun s : ℝ≥0 => x + f s - d s) t :=
    (continuousAt_const.add hfc).sub hdc'
  exact ht hc
