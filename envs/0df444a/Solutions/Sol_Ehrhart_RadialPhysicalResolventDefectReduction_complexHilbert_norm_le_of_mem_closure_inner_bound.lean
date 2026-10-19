-- Prove2me | solution 1 for Ehrhart.RadialPhysicalResolventDefectReduction.complexHilbert_norm_le_of_mem_closure_inner_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/c0dd3e6a-454b-4e68-87d4-24981a2b4438

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.RadialPhysicalResolventDefectReduction
open Set Function Filter MeasureTheory Matrix
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.RadialPhysicalResolventDefectReduction
theorem _root_.solution
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (f : E) (S : Set E) (hf : f ∈ closure S)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ g ∈ S,
      ‖@inner ℂ E _ f g‖ ≤ B * ‖g‖) :
    ‖f‖ ≤ B := by
  let T : Set E :=
    {g : E | ‖@inner ℂ E _ f g‖ ≤ B * ‖g‖}
  have hT : IsClosed T := by
    exact isClosed_le
      ((continuous_const.inner continuous_id).norm)
      (continuous_const.mul continuous_norm)
  have hST : S ⊆ T := by
    intro g hg
    exact hbound g hg
  have hself : f ∈ T := (closure_minimal hST hT) hf
  change ‖@inner ℂ E _ f f‖ ≤ B * ‖f‖ at hself
  have hsq : ‖f‖ ^ 2 ≤ B * ‖f‖ := by
    simpa [inner_self_eq_norm_sq_to_K, norm_pow,
      Complex.norm_real] using hself
  by_cases hfzero : ‖f‖ = 0
  · rw [hfzero]
    exact hB
  · have hfpos : 0 < ‖f‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hfzero)
    nlinarith
end Ehrhart.RadialPhysicalResolventDefectReduction
