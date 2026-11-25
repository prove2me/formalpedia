-- Prove2me | solution 1 for Darpa018.GroupExtension.obstruction_zero_iff_lift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:33:28.86639+00:00
-- url     : https://prove2.me/submissions/39331bda-b75e-4d3e-a7c1-45c5da449262

module
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.Tactic.Abel
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Tactic.NoncommRing
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Tactic.Group
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Definitions.Def_DarpaH2Lifting_Solution
public import Theorems.Thm_Darpa018_H2Core_obstructionClass_zero_iff_section
public import Theorems.Thm_Darpa018_GroupExtension_hasSection_iff_lift

set_option autoImplicit false
@[expose] public section
public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Darpa018 Darpa018.GroupExtension
open scoped IsMulCommutative
variable {G E Q : Type} [Group G] [Group E] [Group Q]
variable (q : E →* Q) [IsMulCommutative q.ker]
variable (ρ : G →* Q) (l : G → E) (hl : ∀ g, q (l g) = ρ g)
namespace Darpa018.GroupExtension
theorem _root_.solution :
    obstruction q ρ l hl = 0 ↔ ∃ f : G →* E, q.comp f = ρ := by
  let := kernelAction q ρ l hl
  rw [obstruction, H2Core.obstructionClass_zero_iff_section]
  exact hasSection_iff_lift q ρ l hl
end Darpa018.GroupExtension
