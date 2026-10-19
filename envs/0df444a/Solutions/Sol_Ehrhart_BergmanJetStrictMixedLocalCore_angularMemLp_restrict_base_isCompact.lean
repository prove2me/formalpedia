-- Prove2me | solution 1 for Ehrhart.BergmanJetStrictMixedLocalCore.angularMemLp_restrict_base_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/980c39ca-316f-4118-91ce-d0ce56a775fb

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetStrictMixedLocalCore
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence
open WeightedTorusDistributionBridge WeightedTorusVectorClosedGraphWeakBridge WeightedTorusDolbeault
open scoped BigOperators ENNReal InnerProductSpace Topology
namespace Ehrhart.BergmanJetStrictMixedLocalCore
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    {g : LogTorus n → ℂ}
    (hg : MemLp g 2 (angularWeightedTorusMeasure a))
    {S : Set (LogTorus n)} (hS : IsCompact S) :
    MemLp g 2 ((sourceTorusBaseMeasure n).restrict S) := by
  have hmeas :
      AEStronglyMeasurable g
        ((sourceTorusBaseMeasure n).restrict S) :=
    (angularMemLp_locallyIntegrable_base
      ha hg).aestronglyMeasurable.mono_measure
        Measure.restrict_le_self
  apply (MeasureTheory.memLp_two_iff_integrable_sq_norm hmeas).mpr
  have hsq :
      Integrable
        (fun q : LogTorus n => ‖g q‖ ^ 2)
        (angularWeightedTorusMeasure a) :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm
      hg.aestronglyMeasurable).mp hg
  have hweighted := hsq.integrableOn (s := S)
  unfold angularWeightedTorusMeasure at hweighted
  change Integrable
    (fun q : LogTorus n => ‖g q‖ ^ 2)
    (((sourceTorusBaseMeasure n).withDensity
      (fun q : LogTorus n =>
        ENNReal.ofReal (angularWeightedTorusDensity a q))).restrict S)
    at hweighted
  rw [restrict_withDensity hS.measurableSet] at hweighted
  have hdmeas :
      Measurable
        (fun q : LogTorus n =>
          ENNReal.ofReal (angularWeightedTorusDensity a q)) :=
    ENNReal.measurable_ofReal.comp
      (continuous_angularWeightedTorusDensity ha).measurable
  have hdfinite :
      ∀ᵐ q : LogTorus n
        ∂((sourceTorusBaseMeasure n).restrict S),
        ENNReal.ofReal (angularWeightedTorusDensity a q) < ⊤ :=
    Filter.Eventually.of_forall
      (fun _ => ENNReal.ofReal_lt_top)
  have hscaled :=
    (integrable_withDensity_iff_integrable_smul'
      hdmeas hdfinite).mp hweighted
  have hexp :
      IntegrableOn
        (fun q : LogTorus n =>
          Real.exp (-a q) * ‖g q‖ ^ 2)
        S (sourceTorusBaseMeasure n) := by
    apply hscaled.congr
    filter_upwards [] with q
    simp [angularWeightedTorusDensity,
      (Real.exp_pos (-a q)).le, smul_eq_mul]
  have hreciprocal :
      Continuous
        (fun q : LogTorus n => Real.exp (a q)) :=
    Real.continuous_exp.comp ha
  have hproduct :=
    hexp.mul_continuousOn hreciprocal.continuousOn hS
  refine hproduct.congr_fun ?_ hS.measurableSet
  intro q hq
  have hcancel :
      Real.exp (-a q) * Real.exp (a q) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    (Real.exp (-a q) * ‖g q‖ ^ 2) * Real.exp (a q) =
      (Real.exp (-a q) * Real.exp (a q)) * ‖g q‖ ^ 2 := by
        ring
    _ = ‖g q‖ ^ 2 := by rw [hcancel, one_mul]
end Ehrhart.BergmanJetStrictMixedLocalCore
