-- Prove2me | solution 1 for CompanionTheory.D.LK.cre_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:28.81855+00:00
-- url     : https://prove2.me/submissions/80bc0874-d0c3-4a18-b734-16a2bb56fec3

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_CreApply
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
import Theorems.Thm_CompanionTheory_D_LK_Car_cre_apply
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
theorem _root_.solution {i : Pos n} {x : Cn n V} {A : Finset (Pos n)} (h : cre i x A ≠ 0) : i ∈ A ∧ x (A.erase i) ≠ 0 := by
  rw [cre_apply] at h
  by_cases hi : i ∈ A
  · exact ⟨hi, fun h0 => h (by simp [h0])⟩
  · simp [hi] at h
end CompanionTheory.D.LK
