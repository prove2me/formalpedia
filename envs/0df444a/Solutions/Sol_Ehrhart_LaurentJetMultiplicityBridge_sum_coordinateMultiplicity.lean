-- Prove2me | solution 1 for Ehrhart.LaurentJetMultiplicityBridge.sum_coordinateMultiplicity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/a2fd3cb2-7960-408d-b359-1a9787ae6b57

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.LaurentJetMultiplicityBridge
open Set Filter Module
open scoped BigOperators Topology
namespace Ehrhart.LaurentJetMultiplicityBridge
theorem _root_.solution {n r : ℕ}
    (q : Fin r → Fin n) :
    (∑ i : Fin n, coordinateMultiplicity q i) = r := by
  classical
  unfold coordinateMultiplicity
  rw [← Fintype.card_sigma]
  exact (Fintype.card_congr (Equiv.sigmaFiberEquiv q)).trans
    (Fintype.card_fin r)
end Ehrhart.LaurentJetMultiplicityBridge
