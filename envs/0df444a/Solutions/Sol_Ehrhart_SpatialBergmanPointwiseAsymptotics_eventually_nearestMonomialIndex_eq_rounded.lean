-- Prove2me | solution 1 for Ehrhart.SpatialBergmanPointwiseAsymptotics.eventually_nearestMonomialIndex_eq_rounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/3be16092-cd29-40a7-9163-8f31d477104b

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TranslatedGaussianLatticeAsymptotics_eventually_roundedLatticeExponent_mem_monomialIndex

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
    ∀ᶠ k : ℕ in atTop,
      (nearestMonomialIndex K u k : Space n) =
        roundedLatticeExponent k u := by
  filter_upwards [eventually_roundedLatticeExponent_mem_monomialIndex
    K hu] with k hk
  simp [nearestMonomialIndex, hk]
end Ehrhart.SpatialBergmanPointwiseAsymptotics
