-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.strictTransform_comap_of_comap_center_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:30:18.472703+00:00
-- url     : https://prove2.me/submissions/da76ed94-0599-4621-82ce-1cece948e198

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransformOffCenter
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coe_complComapSupport
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_strictTransform_comap_complComapSupport___c41640827399

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
theorem _root_.solution {X X₁ B : Scheme.{u}} [IsNoetherian X₁]
    (π : X₁ ⟶ X) (Z D : X.IdealSheafData) (g : B ⟶ X₁)
    (hg : (Z.comap π).comap g = ⊤) :
    (Blowup.strictTransform π Z D).comap g = (D.comap π).comap g := by
  have hsupp : ((((Z.comap π).comap g).support : Closeds B) : Set B)
      = ⇑g.base ⁻¹' (((Z.comap π).support : Closeds X₁) : Set X₁) := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have hempty : ⇑g.base ⁻¹' (((Z.comap π).support : Closeds X₁) : Set X₁) = ∅ := by
    rw [← hsupp, hg]
    simp
  have hbase : ∀ b : B, ⇑g.base b ∈ ((complComapSupport π Z : X₁.Opens) : Set X₁) := by
    intro b
    rw [coe_complComapSupport]
    simp only [Set.mem_compl_iff]
    intro hmem
    have hb : b ∈ ⇑g.base ⁻¹' (((Z.comap π).support : Closeds X₁) : Set X₁) := hmem
    rw [hempty] at hb
    simp at hb
  have hrange : Set.range ⇑g.base ⊆
      Set.range ⇑(Scheme.Opens.ι (complComapSupport π Z)).base := by
    rintro x ⟨b, rfl⟩
    have h0 : ⇑g.base b ∈ ((complComapSupport π Z : X₁.Opens) : Set X₁) := hbase b
    simpa [Scheme.Opens.range_ι] using h0
  have hfac := IsOpenImmersion.lift_fac (Scheme.Opens.ι (complComapSupport π Z)) g hrange
  rw [← hfac, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp,
    strictTransform_comap_complComapSupport_ι]
end FunctorialResolution.EmbeddedResolution
