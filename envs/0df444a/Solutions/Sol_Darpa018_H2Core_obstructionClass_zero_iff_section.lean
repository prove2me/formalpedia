-- Prove2me | solution 1 for Darpa018.H2Core.obstructionClass_zero_iff_section
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:32:53.589279+00:00
-- url     : https://prove2.me/submissions/215e55e3-5260-4a43-aa22-814275d12b9d

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
public import Theorems.Thm_P2M_Darpa018_H2Core_hasSection_iff_isCoboundary__4ff7078dc15b
public import Theorems.Thm_Darpa018_H2Core_obstructionClass_zero_iff_coboundary

set_option autoImplicit false
@[expose] public section
public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Darpa018 Darpa018.H2Core
variable {G M : Type}
variable [Group G] [AddCommGroup M] [DistribMulAction G M]
namespace Darpa018.H2Core
theorem _root_.solution
    (c : G × G → M)
    (hc : groupCohomology.IsCocycle₂ c) :
    obstructionClass c hc = 0 ↔ HasSection c := by
  rw [obstructionClass_zero_iff_coboundary c hc]
  exact (hasSection_iff_isCoboundary₂ c).symm
end Darpa018.H2Core
