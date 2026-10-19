-- Prove2me | solution 1 for Ehrhart.ComplexSaturatedKillingFieldBridge.unweightedTorus_representative_ae_of_complexCover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/5b4416f1-8546-4647-857a-93e3dd712ec7

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusDistributionBridge_unweightedTorusFundamental_measurePreserving
import Theorems.Thm_Ehrhart_WeightedTorusDistributionBridge_angularFundamentalEquiv_symm_apply
import Theorems.Thm_Ehrhart_WeightedTorusDistributionBridge_coverRepresentative_fundamentalCell
import Theorems.Thm_Ehrhart_WeightedTorusDistributionBridge_logarithmicCoordinates_measurePreserving
import Theorems.Thm_Ehrhart_ComplexSaturatedKillingFieldBridge_realFundamentalEmbedding_measurePreserving

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.ComplexSaturatedKillingFieldBridge
open Set Function MeasureTheory Filter
open scoped BigOperators ContDiff Convolution ENNReal InnerProductSpace Topology
open WeightedTorusHilbert WeightedTorusDistributionBridge WeightedTorusGraphWeakBridge
open JointHolomorphicLaurentFourierCompatibility
namespace Ehrhart.ComplexSaturatedKillingFieldBridge
theorem _root_.solution
    {n : ℕ}
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hcover : F =ᵐ[
      (volume : Measure (TorusCharacters.LogSpace n))]
        complexTorusCoverLift f) :
    (fun z : WeightedTorusHilbert.LogTorus n => f z) =ᵐ[
      unweightedTorusMeasure n]
        (fun z => coverRepresentative F z.1 z.2) := by
  have hpush : F =ᵐ[logarithmicCoverPushforward n]
      complexTorusCoverLift f := by
    rw [logarithmicCoverPushforward_eq_smul_volume]
    change F =ᵐ[
      ((logarithmicCoverJacobianFactor n : ℝ≥0∞) •
        (volume : Measure (TorusCharacters.LogSpace n)))]
      complexTorusCoverLift f
    exact (Measure.ae_ennreal_smul_measure_iff
      (ENNReal.coe_ne_zero.mpr
        (logarithmicCoverJacobianFactor_pos n).ne')).mpr hcover
  have hreal :
      (fun p : Space n × Space n =>
        F (logarithmicCoordinatesEquiv n p)) =ᵐ[
          (volume : Measure (Space n × Space n))]
      (fun p => f (realTorusCoverProjection n p)) := by
    have h :=
      (logarithmicCoordinates_measurePreserving n).quasiMeasurePreserving.ae_eq_comp
        hpush
    simpa [Function.comp_def, complexTorusCoverLift,
      complexTorusCoverProjection, realTorusCoverProjection] using h
  let s : Set (Space n) :=
    {t | ∀ i : Fin n, t i ∈ Set.Ioc (0 : ℝ) ((0 : ℝ) + 1)}
  have hrestricted :
      (fun p : Space n × Space n =>
        F (logarithmicCoordinatesEquiv n p)) =ᵐ[
          (volume : Measure (Space n)).prod
            ((volume : Measure (Space n)).restrict s)]
      (fun p => f (realTorusCoverProjection n p)) := by
    have h := ae_restrict_of_ae
      (s := (Set.univ : Set (Space n)) ×ˢ s) hreal
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at h
    simp only [Measure.restrict_univ] at h
    filter_upwards [h] with x hx
    exact hx
  have hfund :=
    (realFundamentalEmbedding_measurePreserving n).quasiMeasurePreserving.ae_eq_comp
      hrestricted
  have htorus :=
    (unweightedTorusFundamental_measurePreserving n).quasiMeasurePreserving.ae_eq_comp
      hfund
  filter_upwards [htorus] with z hz
  have hcell := coverRepresentative_fundamentalCell F z.1
    (angularFundamentalEquiv n z.2)
  have hcoverpoint : coverRepresentative F z.1 z.2 =
      F (logarithmicPoint z.1
        ((angularFundamentalEquiv n z.2) : Space n)) := by
    simpa using hcell
  have hangle :
      angularCoverProjection n
        ((angularFundamentalEquiv n z.2) : Space n) = z.2 := by
    calc
      angularCoverProjection n
          ((angularFundamentalEquiv n z.2) : Space n) =
          (angularFundamentalEquiv n).symm
            (angularFundamentalEquiv n z.2) := by
        rw [angularFundamentalEquiv_symm_apply]
        rfl
      _ = z.2 := (angularFundamentalEquiv n).symm_apply_apply z.2
  rw [hcoverpoint]
  change
    F (logarithmicPoint z.1
      ((angularFundamentalEquiv n z.2) : Space n)) =
      f (z.1, angularCoverProjection n
        ((angularFundamentalEquiv n z.2) : Space n)) at hz
  rw [hangle] at hz
  exact hz.symm
end Ehrhart.ComplexSaturatedKillingFieldBridge
