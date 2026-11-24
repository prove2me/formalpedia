-- Prove2me | solution 1 for FunctorialResolution.Blowup.map_mem_nonZeroDivisors_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:32.805185+00:00
-- url     : https://prove2.me/submissions/b55a39d7-9425-4da7-b33e-859d3bd888b1

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
open FunctorialResolution FunctorialResolution.Blowup
namespace FunctorialResolution.Blowup
theorem _root_.solution {A B : CommRingCat.{u}} (e : A ≅ B) {x : A}
    (hx : x ∈ nonZeroDivisors A) : e.hom.hom x ∈ nonZeroDivisors B := by
  obtain ⟨hx1, hx2⟩ := mem_nonZeroDivisors_iff.mp hx
  have h2 : ∀ z : A, e.inv.hom (e.hom.hom z) = z := by
    intro z
    simp
  have h3 : ∀ y : B, e.hom.hom (e.inv.hom y) = y := by
    intro y
    simp
  have key : ∀ y : B, e.hom.hom x * y = 0 → y = 0 := by
    intro y hy
    have h1 : e.inv.hom (e.hom.hom x * y) = 0 := by rw [hy, map_zero]
    rw [map_mul, h2 x] at h1
    have h4 := hx1 _ h1
    rw [← h3 y, h4, map_zero]
  rw [mem_nonZeroDivisors_iff]
  refine ⟨key, fun y hy => key y ?_⟩
  rw [mul_comm]
  exact hy
end FunctorialResolution.Blowup
