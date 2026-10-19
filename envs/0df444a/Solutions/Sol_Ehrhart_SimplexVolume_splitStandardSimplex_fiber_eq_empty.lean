-- Prove2me | solution 1 for Ehrhart.SimplexVolume.splitStandardSimplex_fiber_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/c08ea229-e8eb-4629-a081-acfa1c311ea3

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.SimplexVolume
open Set MeasureTheory
open scoped BigOperators ENNReal Pointwise
namespace Ehrhart.SimplexVolume
theorem _root_.solution (n : ℕ) {t : ℝ}
    (ht : t < 0 ∨ 1 < t) :
    Prod.mk t ⁻¹' splitStandardSimplex n = ∅ := by
  ext x
  simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
  intro hx
  change 0 ≤ t ∧ (∀ i, 0 ≤ x i) ∧ t + (∑ i, x i) ≤ 1 at hx
  rcases ht with ht | ht
  · linarith [hx.1]
  · have hsum : 0 ≤ ∑ i, x i :=
      Finset.sum_nonneg (fun i _ => hx.2.1 i)
    linarith [hx.2.2]
end Ehrhart.SimplexVolume
