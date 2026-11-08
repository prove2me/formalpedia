-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_ruin8_vcstar_contact_lipschitz_from_positive_band_deriv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T08:47:05.796196+00:00
-- url     : https://prove2.me/submissions/fffeb079-a18e-40fb-b8e2-002a0d3fa375

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_vcstar_unrestricted_verification_regularity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original BV candidate: the positive-band derivative envelope controls a
contact increment whose two endpoints remain in that same interior band. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hbv : X.BoundedVariation) (a b L : ℝ) (ha : 0 < a) (hL : 0 ≤ L)
    (hBound : ∀ z ∈ Set.Icc a b, |deriv (vcstar W) z| ≤ L)
    (z c : ℝ) (hz : z ∈ Set.Icc a b) (hzc : z + c ∈ Set.Icc a b) :
    |vcstar W (z + c) - vcstar W z| ≤ L * |c| ∧
    |deriv (vcstar W) z| ≤ L := by
  have hC : ContDiffOn ℝ 1 (vcstar W) (Set.Ioi 0) :=
    (vcstar_unrestricted_verification_regularity X hX q hq W hW hc
      (Or.inr (Or.inl hbv))).2.2.2.2 hbv
  have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := by
    intro y hy
    exact lt_of_lt_of_le ha hy.1
  have hdiff : ∀ y ∈ Set.Icc a b, DifferentiableAt ℝ (vcstar W) y := by
    intro y hy
    have hypos : y ∈ Set.Ioi (0 : ℝ) := hsub hy
    exact (hC.differentiableOn (by norm_num) y hypos).differentiableAt
      (isOpen_Ioi.mem_nhds hypos)
  have hnorm : ∀ y ∈ Set.Icc a b, ‖deriv (vcstar W) y‖ ≤ L := by
    intro y hy
    simpa [Real.norm_eq_abs] using hBound y hy
  have hmean := (convex_Icc a b : Convex ℝ (Set.Icc a b)).norm_image_sub_le_of_norm_deriv_le
    hdiff hnorm hz hzc
  constructor
  · simpa [Real.norm_eq_abs, add_sub_cancel_left] using hmean
  · exact hBound z hz
