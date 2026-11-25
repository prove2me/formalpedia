-- Prove2me | solution 1 for Darpa018.RepresentationLifting.obstruction_zero_iff_lift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:34:39.734837+00:00
-- url     : https://prove2.me/submissions/e7bc258b-6272-4cef-b156-adda58dde448

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
public import Theorems.Thm_Darpa018_GroupExtension_liftingObstruction_zero_iff_lift

set_option autoImplicit false
@[expose] public section
public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Darpa018 Darpa018.RepresentationLifting
open scoped IsMulCommutative
variable {G R S n : Type} [Group G] [CommRing R] [CommRing S]
variable [Fintype n] [DecidableEq n]
variable (f : R →+* S) (hf : Function.Surjective f)
variable (hsq : ∀ a b : R, f a = 0 → f b = 0 → a * b = 0)
variable (ρ : G →* (Matrix n n S)ˣ)
namespace Darpa018.RepresentationLifting
theorem _root_.solution :
    obstruction f hf hsq ρ = 0 ↔
      ∃ ρ' : G →* (Matrix n n R)ˣ, (reduction f).comp ρ' = ρ := by
  let := MatrixSquareZero.units_map_ker_isMulCommutative (n := n) f hsq
  exact GroupExtension.liftingObstruction_zero_iff_lift (reduction f) ρ
    (MatrixSquareZero.units_map_surjective_of_squareZeroKernel f hf hsq)
end Darpa018.RepresentationLifting
