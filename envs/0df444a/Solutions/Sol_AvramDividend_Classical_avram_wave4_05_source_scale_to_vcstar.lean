-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_scale_to_vcstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:25:42.203876+00:00
-- url     : https://prove2.me/submissions/610897ca-10c3-4aeb-b7d2-85bedd69ec6b

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_vcstar_interior_harmonicity_of_scale_harmonicity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
/-- Pointwise full source scale harmonicity transfers to the genuine candidate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hc : 0 < cstar W)
    (hscale : ∀ x : ℝ, 0 < x →
      X.GeneratorIntegrable W x ∧ X.generator W x - q * W x = 0) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) x ∧
        X.generator (vcstar W) x - q * vcstar W x = 0 := by
  have hfin := cstar_lt_top X hX q hq W hW
  have ha : 0 < (cstar W).toReal :=
    ENNReal.toReal_pos (ne_of_gt hc) (ne_of_lt hfin)
  exact vcstar_interior_harmonicity_of_scale_harmonicity
    X q W hW ha (by
      intro x hx
      exact hscale x hx.1)
