-- Prove2me | solution 1 for Ehrhart.SpatialBergmanPointwiseAsymptotics.tendsto_nearestMonomialIndex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/96e5c485-94d6-4d0f-83d0-7cff54f3c6af

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TranslatedGaussianLatticeAsymptotics_tendsto_roundedLatticeExponent
import Theorems.Thm_Ehrhart_SpatialBergmanPointwiseAsymptotics_eventually_nearestMonomialIndex_eq_rounded

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.SpatialBergmanPointwiseAsymptotics
open Set Filter MeasureTheory Matrix
open scoped Topology BigOperators
open TranslatedGaussianLatticeAsymptotics
namespace Ehrhart.SpatialBergmanPointwiseAsymptotics
theorem _root_.solution {n : ℕ}
    (K : CenteredBody n)
    {u : Space n} (hu : u ∈ interior K.carrier) :
    Tendsto (fun k : ℕ =>
      (nearestMonomialIndex K u k : Space n))
      atTop (𝓝 u) := by
  refine Filter.Tendsto.congr' ?_
    (tendsto_roundedLatticeExponent u)
  filter_upwards [eventually_nearestMonomialIndex_eq_rounded K hu]
    with k hk
  exact hk.symm
end Ehrhart.SpatialBergmanPointwiseAsymptotics
