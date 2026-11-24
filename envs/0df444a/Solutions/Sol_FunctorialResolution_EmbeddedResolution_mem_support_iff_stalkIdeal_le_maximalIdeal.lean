-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.mem_support_iff_stalkIdeal_le_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:12:12.070279+00:00
-- url     : https://prove2.me/submissions/895eef9e-c180-4be6-8c2c-7f5e01ab192e

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_eq_map_germ
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_affineOpens_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace FunctorialResolution.EmbeddedResolution
open AlgebraicGeometry TopologicalSpace
universe u
variable {X : Scheme.{u}}
private theorem germ_mem_maximalIdeal_iff_not_mem_basicOpen {X : Scheme.{u}} (x : X) (U : X.Opens) (hxU : x ∈ U)
    (f : Γ(X, U)) :
    (X.presheaf.germ U x hxU).hom f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ↔
      x ∉ X.basicOpen f := by
  have h := AlgebraicGeometry.Scheme.mem_basicOpen X f x hxU
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hn hx
    exact hn (h.mp hx)
  · intro hn hu
    exact hn (h.mpr hu)
private theorem mem_support_iff_forall_germ_mem_maximalIdeal {X : Scheme.{u}}
    (I : X.IdealSheafData) (x : X) (U : X.affineOpens) (hxU : x ∈ U.1) :
    x ∈ I.support ↔ ∀ f ∈ I.ideal U,
      (X.presheaf.germ U.1 x hxU).hom f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  rw [AlgebraicGeometry.Scheme.IdealSheafData.mem_support_iff_of_mem (I := I) (U := U) hxU,
    AlgebraicGeometry.Scheme.mem_zeroLocus_iff]
  constructor
  · intro h f hf
    exact (germ_mem_maximalIdeal_iff_not_mem_basicOpen x U.1 hxU f).mpr (h f hf)
  · intro h f hf
    exact (germ_mem_maximalIdeal_iff_not_mem_basicOpen x U.1 hxU f).mp (h f hf)
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open AlgebraicGeometry TopologicalSpace
universe u
variable {X : Scheme.{u}}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (I : X.IdealSheafData) (x : X) :
    x ∈ I.support ↔ stalkIdeal I x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  obtain ⟨U, hxU0⟩ := X.exists_affineOpens_mem x
  have hxU : x ∈ U.1 := hxU0
  rw [stalkIdeal_eq_map_germ I x U hxU, Ideal.map_le_iff_le_comap,
    mem_support_iff_forall_germ_mem_maximalIdeal I x U hxU]
  constructor
  · intro h f hf
    exact h f hf
  · intro h f hf
    exact h hf
end FunctorialResolution.EmbeddedResolution
