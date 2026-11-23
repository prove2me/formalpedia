-- Prove2me | solution 1 for CompanionTheory.D.LK.ann_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:28:08.182397+00:00
-- url     : https://prove2.me/submissions/9553a6d8-be83-4c75-a08e-7df439244bb6

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_CreApply
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
import Theorems.Thm_CompanionTheory_D_LK_Car_ann_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Finset
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open Car Formalism.REAL
variable {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace CompanionTheory.D.LK
theorem _root_.solution {i : Pos n} {x : Cn n V} {A : Finset (Pos n)} (h : ann i x A ≠ 0) : i ∉ A ∧ x (insert i A) ≠ 0 := by
  rw [ann_apply] at h
  by_cases hi : i ∈ A
  · simp [hi] at h
  · exact ⟨hi, fun h0 => h (by simp [h0])⟩
end CompanionTheory.D.LK
