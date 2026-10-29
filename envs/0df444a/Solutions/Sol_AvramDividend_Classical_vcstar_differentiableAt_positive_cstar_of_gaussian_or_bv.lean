-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_differentiableAt_positive_cstar_of_gaussian_or_bv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T08:17:11.417703+00:00
-- url     : https://prove2.me/submissions/64b302a9-ecb1-417b-ac7d-89aaf1460297

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.NormNum
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_global_C1_bv_positive_barrier
import Theorems.Thm_AvramDividend_Classical_vcstar_global_C2_gaussian_positive_barrier
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hregular : 0 < X.σ ∨ X.BoundedVariation) :
    DifferentiableAt ℝ (vcstar W) (cstar W).toReal := by
  have ha : 0 < (cstar W).toReal :=
    ENNReal.toReal_pos (ne_of_gt hcpos) (ne_of_lt hc)
  have hmem : (cstar W).toReal ∈ Ioi (0 : ℝ) := Set.mem_Ioi.mpr ha
  rcases hregular with hgaussian | hbv
  · have hCtwo : ContDiffOn ℝ 2 (vcstar W) (Ioi (0 : ℝ)) :=
      vcstar_global_C2_gaussian_positive_barrier X hX q hq W hW hc hcpos hgaussian
    have hdiffOn : DifferentiableOn ℝ (vcstar W) (Ioi (0 : ℝ)) :=
      hCtwo.differentiableOn (by norm_num)
    exact (hdiffOn _ hmem).differentiableAt (isOpen_Ioi.mem_nhds hmem)
  · have hCone : ContDiffOn ℝ 1 (vcstar W) (Ioi (0 : ℝ)) :=
      vcstar_global_C1_bv_positive_barrier X hX q hq W hW hc hcpos hbv
    have hdiffOn : DifferentiableOn ℝ (vcstar W) (Ioi (0 : ℝ)) :=
      hCone.differentiableOn (by norm_num)
    exact (hdiffOn _ hmem).differentiableAt (isOpen_Ioi.mem_nhds hmem)
