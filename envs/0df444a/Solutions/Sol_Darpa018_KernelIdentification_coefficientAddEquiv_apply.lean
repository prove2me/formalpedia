-- Prove2me | solution 1 for Darpa018.KernelIdentification.coefficientAddEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:32:06.457942+00:00
-- url     : https://prove2.me/submissions/e2363eb1-6b9f-4f64-9a90-0083476c0b68

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
open Darpa018 Darpa018.KernelIdentification
universe u v w
variable {R : Type u} {S : Type v} {n : Type w}
variable [CommRing R] [CommRing S] [Fintype n] [DecidableEq n]
namespace Darpa018.KernelIdentification
theorem _root_.solution (f : R →+* S)
    (hsq : ∀ a b : R, f a = 0 → f b = 0 → a * b = 0)
    (u : Additive (reduction (n := n) f).ker) (i j : n) :
    ((coefficientAddEquiv f hsq u) i j).val =
      ((u.toMul.val : Matrix n n R) - 1) i j := rfl
end Darpa018.KernelIdentification
