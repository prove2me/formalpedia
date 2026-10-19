-- Prove2me | solution 1 for Ehrhart.BergmanJetUpperEnvelope.eventually_momentJointTailSup_le_majorant_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/de800601-c96d-4744-9cbe-fd551536713b

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetUpperEnvelope
open Set Function Filter MeasureTheory Module
open MomentOptimizer MomentFirstVariation MomentTargetGeodesic MomentRegularity MomentWeakBergman
open BergmanJetGeodesic BergmanJetRealGeodesic ActualJetUpperEnvelope
open scoped BigOperators ENNReal InnerProductSpace Topology
namespace Ehrhart.BergmanJetUpperEnvelope
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ q : PositiveJointLogSpace n,
      momentJointTailSup K F htransport p r q ≤
        momentJointMajorant K F q + ε := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (eventually_momentPositiveJointGeodesic_le_majorant_add
      K F htransport p hε)
  filter_upwards [eventually_ge_atTop N] with r hr q
  unfold momentJointTailSup
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨j, rfl⟩
  exact hN _ (by omega) q
end Ehrhart.BergmanJetUpperEnvelope
