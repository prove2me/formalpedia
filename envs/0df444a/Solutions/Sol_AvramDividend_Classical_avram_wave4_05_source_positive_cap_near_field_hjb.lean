-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_positive_cap_near_field_hjb
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:28:52.796702+00:00
-- url     : https://prove2.me/submissions/80050c1d-024e-4492-95a2-0fa9569e39aa

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one
import Theorems.Thm_AvramDividend_Classical_vcstar_continuousOn_Icc_below_positive_cstar
import Theorems.Thm_AvramDividend_Classical_left_affine_majorant_of_deriv_ge_one
import Theorems.Thm_AvramDividend_Classical_vcstar_near_HJB_of_affine_majorant_at_threshold
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The original derivative inequality eliminates the near-field affine
majorant premise, leaving only source Standing and the sharp drift threshold. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hpos : 0 < (cstar W).toReal)
    (x : ℝ) (hx : (cstar W).toReal < x) (hx1 : 1 ≤ x)
    (hthreshold : (cstar W).toReal + max 0 (X.c / q) ≤ x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      max (X.generator (vcstar W) x - q * vcstar W x)
        (1 - deriv (vcstar W) x) = 0 := by
  have hcont :
      ContinuousOn (vcstar W) (Icc 0 (cstar W).toReal) :=
    vcstar_continuousOn_Icc_below_positive_cstar X q W hW hpos
  have hdiff : ∀ z ∈ Ioo (0 : ℝ) (cstar W).toReal,
      DifferentiableAt ℝ (vcstar W) z := by
    intro z hz
    exact (vcstar_deriv_ge_one X hX q hq W hW z hz.1).1
  have hder : ∀ z ∈ Ioo (0 : ℝ) (cstar W).toReal,
      1 ≤ deriv (vcstar W) z := by
    intro z hz
    exact (vcstar_deriv_ge_one X hX q hq W hW z hz.1).2
  have hchord :=
    left_affine_majorant_of_deriv_ge_one
      (vcstar W) (cstar W).toReal (le_of_lt hpos) hcont hdiff hder
  exact vcstar_near_HJB_of_affine_majorant_at_threshold
    X q hq W hW hpos hchord x hx hx1 hthreshold
