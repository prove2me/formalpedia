-- Prove2me | solution 1 for FunctorialResolution.Blowup.comap_ker_comp_of_isOpenImmersion
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:44.536637+00:00
-- url     : https://prove2.me/submissions/57dfc1c3-4c2c-4af6-acb0-b071a8c0cb77

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ideal_eq_map_appLE

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
theorem _root_.solution {A B C : Scheme.{u}} (j : A ⟶ B) (f : B ⟶ C)
    [IsOpenImmersion f] [QuasiCompact j] [QuasiCompact (j ≫ f)] :
    (j ≫ f).ker.comap f = j.ker := by
  refine Scheme.IdealSheafData.ext ?_
  funext V
  have hU : IsAffineOpen (f ''ᵁ V.1) := V.2.image_of_isOpenImmersion f
  have hpre : f ⁻¹ᵁ (f ''ᵁ V.1) = V.1 := f.preimage_image_eq V.1
  have e : (V : B.Opens) ≤ f ⁻¹ᵁ (f ''ᵁ V.1) := hpre.ge
  have hopeq : j ⁻¹ᵁ V.1 = (j ≫ f) ⁻¹ᵁ (f ''ᵁ V.1) := by
    show j ⁻¹ᵁ V.1 = j ⁻¹ᵁ (f ⁻¹ᵁ (f ''ᵁ V.1))
    rw [hpre]
  have hop : j ⁻¹ᵁ V.1 ≤ (j ≫ f) ⁻¹ᵁ (f ''ᵁ V.1) := hopeq.le
  have key : f.appLE (f ''ᵁ V.1) V.1 e ≫ j.app V.1
      = (j ≫ f).app (f ''ᵁ V.1) ≫ A.presheaf.map (homOfLE hop).op := by
    rw [Scheme.Hom.app_eq_appLE j]
    exact Scheme.Hom.appLE_comp_appLE j f (f ''ᵁ V.1) V.1 (j ⁻¹ᵁ V.1) e le_rfl
  have keyr : ∀ x, (CommRingCat.Hom.hom (j.app V.1))
        ((CommRingCat.Hom.hom (f.appLE (f ''ᵁ V.1) V.1 e)) x)
      = (CommRingCat.Hom.hom (A.presheaf.map (homOfLE hop).op))
        ((CommRingCat.Hom.hom ((j ≫ f).app (f ''ᵁ V.1))) x) := by
    intro x
    have h' := congrArg (fun m => (CommRingCat.Hom.hom m) x) key
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using h'
  have hρ : ∀ y, (CommRingCat.Hom.hom (A.presheaf.map (homOfLE hop).op)) y = 0 → y = 0 := by
    intro y hy
    have hcomp : A.presheaf.map (homOfLE hop).op ≫ A.presheaf.map (homOfLE hopeq.ge).op
        = 𝟙 (A.presheaf.obj (Opposite.op ((j ≫ f) ⁻¹ᵁ (f ''ᵁ V.1)))) := by
      rw [← CategoryTheory.Functor.map_comp, ← op_comp,
        Subsingleton.elim (homOfLE hopeq.ge ≫ homOfLE hop) (𝟙 _), op_id,
        CategoryTheory.Functor.map_id]
    have h2 := congrArg (fun m => (CommRingCat.Hom.hom m) y) hcomp
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply,
      hy, map_zero] at h2
    exact h2.symm
  have hφ : Function.Surjective (CommRingCat.Hom.hom (f.appLE (f ''ᵁ V.1) V.1 e)) := by
    have : IsIso (f.appLE (f ''ᵁ V.1) V.1 e) := by
      rw [← Scheme.Hom.appIso_hom' f V.1]
      infer_instance
    intro y
    refine ⟨(CommRingCat.Hom.hom (inv (f.appLE (f ''ᵁ V.1) V.1 e))) y, ?_⟩
    have h3 := congrArg (fun m => (CommRingCat.Hom.hom m) y)
      (IsIso.inv_hom_id (f.appLE (f ''ᵁ V.1) V.1 e))
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id,
      RingHom.id_apply] using h3
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE _ f ⟨f ''ᵁ V.1, hU⟩ V e,
    Scheme.Hom.ker_apply, Scheme.Hom.ker_apply]
  dsimp only
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, keyr x]
    rw [RingHom.mem_ker] at hx
    rw [hx, map_zero]
  · intro y hy
    obtain ⟨x, rfl⟩ := hφ y
    apply Ideal.mem_map_of_mem
    rw [RingHom.mem_ker] at hy ⊢
    exact hρ _ ((keyr x).symm.trans hy)
end FunctorialResolution.Blowup
