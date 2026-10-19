-- Prove2me | solution 1 for Ehrhart.MonomialDivergence.not_integrable_monomialWeight_of_centeredBody_not_mem_interior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/a0f0bd93-9110-46bc-9cfb-f62b404971ec

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MonomialDivergence_not_integrable_monomialWeight_of_not_mem_interior

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.MonomialDivergence
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace Ehrhart.MonomialDivergence
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    {u : Space n} (hu : u ∉ interior K.carrier)
    {φ : Space n → ℝ} {C : ℝ}
    (hupper : ∀ x : Space n,
      φ x ≤ SupportFunction.supportFunction K.carrier x + C)
    {k : ℝ} (hk : 0 < k) :
    ¬ Integrable (MonomialIntegrability.monomialWeight k u φ)
      (volume : Measure (Space n)) :=
  not_integrable_monomialWeight_of_not_mem_interior
    K.compact K.convex K.fullDimensional hu hupper hk
end Ehrhart.MonomialDivergence
