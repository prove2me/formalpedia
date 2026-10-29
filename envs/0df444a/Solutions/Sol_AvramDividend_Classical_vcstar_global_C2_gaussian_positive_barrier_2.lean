-- Prove2me | solution 2 for AvramDividend.Classical.vcstar_global_C2_gaussian_positive_barrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:55:28.470038+00:00
-- url     : https://prove2.me/submissions/22dc0257-d320-45cb-9ca0-df7530916cde

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_vcstar_global_C2_gaussian_of_positive_tilt
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hσ : 0 < X.σ) :
    ContDiffOn ℝ 2 (vcstar W) (Ioi 0) := by
  obtain ⟨_, φ, hφ, hmono⟩ :=
    scaleFunction_tilted_positive_monotone X hX q hq W hW
  exact vcstar_global_C2_gaussian_of_positive_tilt X hX q hq W hW
    (ENNReal.toReal_pos hcpos.ne' hc.ne) hσ ⟨φ, hφ, hmono⟩
