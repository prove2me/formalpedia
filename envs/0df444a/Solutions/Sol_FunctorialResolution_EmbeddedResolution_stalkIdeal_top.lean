-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.stalkIdeal_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:53.864643+00:00
-- url     : https://prove2.me/submissions/40ece49a-dd4f-413f-ab38-18a202971ae2

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_affineOpens_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open AlgebraicGeometry TopologicalSpace
universe u
variable {X : Scheme.{u}}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (x : X) : stalkIdeal (⊤ : X.IdealSheafData) x = ⊤ := by
  obtain ⟨U, hxU⟩ := X.exists_affineOpens_mem x
  have h1 : (1 : Γ(X, U.1)) ∈ (⊤ : X.IdealSheafData).ideal U := by simp
  have h3 : Ideal.map (X.presheaf.germ U.1 x hxU).hom ((⊤ : X.IdealSheafData).ideal U) ≤
      stalkIdeal (⊤ : X.IdealSheafData) x :=
    le_iSup (fun V : {V : X.affineOpens // x ∈ V.1.1} =>
      Ideal.map (X.presheaf.germ V.1.1 x V.2).hom ((⊤ : X.IdealSheafData).ideal V.1)) ⟨U, hxU⟩
  have h2 := Ideal.mem_map_of_mem (X.presheaf.germ U.1 x hxU).hom h1
  rw [map_one] at h2
  exact (Ideal.eq_top_iff_one _).mpr (SetLike.le_def.mp h3 h2)
end FunctorialResolution.EmbeddedResolution
