-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_cstar_positive_boundary_regularity_package
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T18:18:33.159235+00:00
-- url     : https://prove2.me/submissions/56997a2a-95ba-489d-b74a-d7ce962bca57
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos_of_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_two_of_gaussian
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_continuous_of_gaussian
import Theorems.Thm_AvramDividend_Classical_deriv_deriv_eq_zero_at_positive_cstar_of_deriv_continuous

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

/-- Integrate Standing C1, tilted derivative positivity and Gaussian C2
    into the positive finite optimal-barrier regularity package. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W) :
    (∀ y : ℝ, 0 < y → DifferentiableAt ℝ W y) ∧
    deriv W (cstar W).toReal ≠ 0 ∧
    (X.σ ≠ 0 → HasDerivAt (deriv W) 0 (cstar W).toReal) := by
  have ha : 0 < (cstar W).toReal :=
    (ENNReal.toReal_pos_iff).mpr ⟨hcpos, hc⟩
  have hC1 := scaleFunction_contDiff_one_of_standing X hX q hq W hW
  have hdiff : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ W y := by
    intro y hy
    exact (hC1.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hy)
  obtain ⟨hpos, htilt⟩ :=
    scaleFunction_tilted_positive_monotone X hX q hq W hW
  have hnormal : 0 < deriv W (cstar W).toReal :=
    scaleDeriv_pos_of_tilted_positive_monotone
      X hX q hq W hW hpos hdiff htilt _ ha
  refine ⟨hdiff, ne_of_gt hnormal, ?_⟩
  intro hσ
  have hsig : 0 < X.σ := lt_of_le_of_ne X.σ_nonneg hσ.symm
  have hC2 := scaleFunction_contDiff_two_of_gaussian X hX q hq W hW hsig
  have hderivcont := scaleDeriv_continuous_of_gaussian X hsig q hq W hW
  have hzero := deriv_deriv_eq_zero_at_positive_cstar_of_deriv_continuous
    W hderivcont ha
  have hD1 : ContDiffOn ℝ 1 (deriv W) (Ioi 0) :=
    hC2.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hderivdiff : DifferentiableAt ℝ (deriv W) (cstar W).toReal :=
    (hD1.differentiableOn one_ne_zero).differentiableAt
      (isOpen_Ioi.mem_nhds ha)
  simpa only [hzero] using hderivdiff.hasDerivAt
