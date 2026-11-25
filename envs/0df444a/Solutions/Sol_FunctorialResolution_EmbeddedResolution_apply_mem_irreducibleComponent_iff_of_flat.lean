-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.apply_mem_irreducibleComponent_iff_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:22:03.111413+00:00
-- url     : https://prove2.me/submissions/96e02129-a667-4c17-ae97-d94d2c4fc0c3

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_IrreducibleComponentsFlatPreimage
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_apply_mem_irreducibleComponent_iff_of_generalizingMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.Flat f]
    {C : Set ↥Y} (hC : C ∈ irreducibleComponents ↥Y) (x : ↥X) :
    (fun x : ↥X => f x) x ∈ C ↔
      ∃ C' : Set ↥X, C' ∈ irreducibleComponents ↥X ∧ x ∈ C' ∧
        closure ((fun x : ↥X => f x) '' C') = C := by
  have hf : GeneralizingMap (fun x : ↥X => f x) :=
    AlgebraicGeometry.Flat.generalizingMap (f := f)
  exact apply_mem_irreducibleComponent_iff_of_generalizingMap f hf hC x
end FunctorialResolution.EmbeddedResolution
