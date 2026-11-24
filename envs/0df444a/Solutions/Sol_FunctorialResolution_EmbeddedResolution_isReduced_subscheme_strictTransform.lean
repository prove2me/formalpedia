-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isReduced_subscheme_strictTransform
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:14:31.669464+00:00
-- url     : https://prove2.me/submissions/963dc5ab-986c-402d-ba77-60ebeee125ed

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupIsoOffCenter
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_OpenImmersionAppLE
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_ReducedSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransform
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_strictTransform_eq_ker_strictTransform__ddf54f1c1d60
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_exists_iso_subscheme_comap_of_isIso
import Theorems.Thm_FunctorialResolution_Blowup_IsBlowupAlongIdealSheaf_isIso_of_top
import Theorems.Thm_FunctorialResolution_Blowup_IsBlowupAlongIdealSheaf_restrict
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isReduced_subscheme_ker
import Theorems.Thm_P2M_FunctorialResolution_Blowup_comap___support_compl_eq_top_7d133a646fc9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
private theorem ker_morphismRestrict_subschemeι {T : Scheme.{u}} (K : T.IdealSheafData) (V : T.Opens) :
    (K.subschemeι ∣_ V).ker = K.comap (Scheme.Opens.ι V) := by
  have h := isPullback_morphismRestrict K.subschemeι V
  have hfac : h.isoPullback.hom ≫ Limits.pullback.fst (Scheme.Opens.ι V) K.subschemeι
      = K.subschemeι ∣_ V := h.isoPullback_hom_fst
  show (K.subschemeι ∣_ V).ker = (Limits.pullback.fst (Scheme.Opens.ι V) K.subschemeι).ker
  rw [← hfac, Scheme.Hom.ker_comp_of_isIso]
private theorem exists_isIso_subschemeι_preimage_comap {T : Scheme.{u}} (K : T.IdealSheafData) (V : T.Opens) :
    ∃ e : (K.subschemeι ⁻¹ᵁ V).toScheme ⟶ (K.comap (Scheme.Opens.ι V)).subscheme,
      IsIso e ∧ e ≫ (K.comap (Scheme.Opens.ι V)).subschemeι = K.subschemeι ∣_ V := by
  have hk : (K.subschemeι ∣_ V).ker = (K.comap (Scheme.Opens.ι V)).subschemeι.ker := by
    rw [ker_morphismRestrict_subschemeι, Scheme.IdealSheafData.ker_subschemeι]
  refine ⟨IsClosedImmersion.lift (K.comap (Scheme.Opens.ι V)).subschemeι
      (K.subschemeι ∣_ V) (le_of_eq hk.symm), ?_, IsClosedImmersion.lift_fac _ _ _⟩
  exact IsClosedImmersion.isIso_of_ker_eq (K.subschemeι ∣_ V)
    (K.comap (Scheme.Opens.ι V)).subschemeι _ (IsClosedImmersion.lift_fac _ _ _) hk
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) (h : Blowup.IsBlowupAlongIdealSheaf π Z) [IsReduced D.subscheme]
    [QuasiCompact (strictTransformι π Z D)] :
    IsReduced (Blowup.strictTransform π Z D).subscheme := by
  have h1 := h.restrict Z.support.compl
  rw [Blowup.comap_ι_support_compl_eq_top Z] at h1
  have : IsIso (π ∣_ Z.support.compl) := h1.isIso_of_top
  have hsupp : (Z.comap π).support.compl = π ⁻¹ᵁ Z.support.compl := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have hcc : (D.comap π).comap (Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl))
      = (D.comap (Scheme.Opens.ι Z.support.compl)).comap (π ∣_ Z.support.compl) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      morphismRestrict_ι]
  obtain ⟨e₁, he₁, -⟩ := exists_isIso_subschemeι_preimage_comap (D.comap π) (π ⁻¹ᵁ Z.support.compl)
  obtain ⟨e₂, he₂, -⟩ :=
    Scheme.IdealSheafData.exists_iso_subscheme_comap_of_isIso (π ∣_ Z.support.compl)
      (D.comap (Scheme.Opens.ι Z.support.compl))
  obtain ⟨e₃, he₃, -⟩ := exists_isIso_subschemeι_preimage_comap D Z.support.compl
  have := he₁
  have := he₂
  have := he₃
  have : IsReduced (D.subschemeι ⁻¹ᵁ Z.support.compl).toScheme :=
    isReduced_of_isOpenImmersion (Scheme.Opens.ι (D.subschemeι ⁻¹ᵁ Z.support.compl))
  have : IsReduced (D.comap (Scheme.Opens.ι Z.support.compl)).subscheme :=
    isReduced_of_isOpenImmersion (inv e₃)
  have : IsReduced
      ((D.comap (Scheme.Opens.ι Z.support.compl)).comap (π ∣_ Z.support.compl)).subscheme :=
    isReduced_of_isOpenImmersion e₂
  have : IsReduced ((D.comap π).comap (Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl))).subscheme := by
    rw [hcc]; infer_instance
  have : IsReduced (strictTransformOpens π Z D).toScheme := by
    have hrw : strictTransformOpens π Z D
        = (D.comap π).subschemeι ⁻¹ᵁ (π ⁻¹ᵁ Z.support.compl) := by
      show (D.comap π).subschemeι ⁻¹ᵁ (Z.comap π).support.compl
          = (D.comap π).subschemeι ⁻¹ᵁ (π ⁻¹ᵁ Z.support.compl)
      rw [hsupp]
    rw [hrw]
    exact isReduced_of_isOpenImmersion e₁
  rw [strictTransform_eq_ker_strictTransformι]
  exact isReduced_subscheme_ker _
end FunctorialResolution.EmbeddedResolution
