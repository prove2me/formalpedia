-- Prove2me | solution 1 for Ehrhart.MonomialDivergence.exists_separating_direction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/0c925729-0c7e-4f0f-8601-2c069501708e

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

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
theorem _root_.solution {n : ℕ}
    {K : Set (Space n)} (hconvex : Convex ℝ K)
    (hinterior : (interior K).Nonempty)
    {u : Space n} (hu : u ∉ interior K) :
    ∃ v : Space n, v ≠ 0 ∧
      ∀ y ∈ K, SupportFunction.pairing y v ≤
        SupportFunction.pairing u v := by
  obtain ⟨f, hf, hseparate⟩ :=
    geometric_hahn_banach_of_nonempty_interior_point
      hconvex hu hinterior
  refine ⟨dualVector f, ?_, fun y hy => ?_⟩
  · intro hv
    apply hf
    ext x
    rw [dual_apply_eq_pairing, hv]
    simp [SupportFunction.pairing]
  · simpa [dual_apply_eq_pairing] using hseparate y hy
end Ehrhart.MonomialDivergence
