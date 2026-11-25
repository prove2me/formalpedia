-- Prove2me | solution 1 for Darpa018.H2Core.obstructionClass_zero_iff_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:31:52.404893+00:00
-- url     : https://prove2.me/submissions/2ab2e274-48dd-4997-bc5e-f46a30cbd49c

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
    obstructionClass c hc = 0 ↔ groupCohomology.IsCoboundary₂ c := by
  unfold obstructionClass
  rw [groupCohomology.H2π_eq_zero_iff]
  constructor
  · intro h
    exact groupCohomology.isCoboundary₂_of_mem_coboundaries₂ (k := ℤ) c h
  · intro h
    exact (groupCohomology.coboundariesOfIsCoboundary₂ (k := ℤ) h).property
end Darpa018.H2Core
