-- Prove2me | solution 1 for Ehrhart.WeightedTorusDistributionBridge.weightedScalarL2_locallyIntegrable_unweighted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/44bda13e-452f-492e-8534-f260949eedb8

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusDistributionBridge_radialWeight_lt_top
import Theorems.Thm_Ehrhart_WeightedTorusDistributionBridge_weightedTorusMeasure_eq_unweighted_withDensity
import Theorems.Thm_Ehrhart_WeightedTorusDistributionBridge_weightedScalarL2_locallyIntegrable_weighted

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusDistributionBridge
open Set Function MeasureTheory Filter
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution
attribute [local instance] Ehrhart.WeightedTorusDistributionBridge._p2m_local_instance_3610026555_18903
attribute [local instance] Ehrhart.WeightedTorusDistributionBridge._p2m_local_instance_3610026555_18906
namespace Ehrhart.WeightedTorusDistributionBridge
theorem _root_.solution {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ)
    (f : WeightedTorusHilbert.weightedHilbert k φ) :
    LocallyIntegrable
      (fun z : WeightedTorusHilbert.LogTorus n => f z)
      (unweightedTorusMeasure n) := by
  let g : WeightedTorusHilbert.LogTorus n → ℂ :=
    fun z => f z
  change LocallyIntegrable g (unweightedTorusMeasure n)
  apply locallyIntegrable_iff.mpr
  intro K hK
  have hweighted : IntegrableOn g K
      (WeightedTorusHilbert.weightedTorusMeasure k φ) := by
    exact (weightedScalarL2_locallyIntegrable_weighted hφ f).integrableOn_isCompact hK
  rw [weightedTorusMeasure_eq_unweighted_withDensity hφ] at hweighted
  change Integrable
    g
    (((unweightedTorusMeasure n).withDensity
      (fun z : WeightedTorusHilbert.LogTorus n =>
        WeightedTorusHilbert.radialWeight k φ z.1)).restrict K)
    at hweighted
  rw [restrict_withDensity hK.isClosed.measurableSet] at hweighted
  have hdmeas : Measurable
      (fun z : WeightedTorusHilbert.LogTorus n =>
        WeightedTorusHilbert.radialWeight k φ z.1) :=
    (WeightedTorusHilbert.radialWeight_measurable k hφ).comp
      measurable_fst
  have hdfinite :
      ∀ᵐ z : WeightedTorusHilbert.LogTorus n
        ∂((unweightedTorusMeasure n).restrict K),
        WeightedTorusHilbert.radialWeight k φ z.1 < ⊤ :=
    Filter.Eventually.of_forall (fun z => radialWeight_lt_top φ z.1)
  have hscaled :=
    (integrable_withDensity_iff_integrable_smul'
      hdmeas hdfinite).mp hweighted
  have hexp : IntegrableOn
      (fun z : WeightedTorusHilbert.LogTorus n =>
        (Real.exp (-(k : ℝ) * φ z.1) : ℂ) * g z)
      K (unweightedTorusMeasure n) := by
    apply hscaled.congr
    filter_upwards [] with z
    simp [WeightedTorusHilbert.radialWeight,
      (Real.exp_pos _).le, Complex.real_smul]
  have hreciprocal : Continuous
      (fun z : WeightedTorusHilbert.LogTorus n =>
        (Real.exp ((k : ℝ) * φ z.1) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp
        (continuous_const.mul (hφ.comp continuous_fst)))
  have hproduct := hexp.mul_continuousOn
    hreciprocal.continuousOn hK
  refine hproduct.congr_fun ?_ hK.isClosed.measurableSet
  intro z hz
  have hcancel :
      (Real.exp (-(k : ℝ) * φ z.1) : ℂ) *
        (Real.exp ((k : ℝ) * φ z.1) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    have ha : -(k : ℝ) * φ z.1 + (k : ℝ) * φ z.1 = 0 := by ring
    rw [ha]
    simp
  calc
    ((Real.exp (-(k : ℝ) * φ z.1) : ℂ) * g z) *
        (Real.exp ((k : ℝ) * φ z.1) : ℂ) =
      ((Real.exp (-(k : ℝ) * φ z.1) : ℂ) *
        (Real.exp ((k : ℝ) * φ z.1) : ℂ)) * g z := by ring
    _ = g z := by rw [hcancel, one_mul]
end Ehrhart.WeightedTorusDistributionBridge
