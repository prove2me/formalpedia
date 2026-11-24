-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.exists_iso_subscheme_vanishingIdeal_of_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:47:43.414506+00:00
-- url     : https://prove2.me/submissions/fc6950cd-a72f-4c80-9816-2231b9a638f6

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_ClopenSubscheme
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
namespace AlgebraicGeometry.Scheme.Opens
end AlgebraicGeometry.Scheme.Opens
namespace FunctorialResolution.EmbeddedResolution
private theorem exists_iso_subscheme_vanishingIdeal_of_coe_eq {X : Scheme} [IsReduced X]
    (C : X.Opens) (Z : Closeds X) (hZ : (Z : Set X) = (C : Set X)) :
    ∃ e : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≅ C.toScheme,
      e.hom ≫ C.ι = (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι := by
  have hCclosed : IsClosed (C : Set X) := by rw [← hZ]; exact Z.2
  have : IsClosedImmersion C.ι :=
    IsClosedImmersion.of_isPreimmersion C.ι (by rw [C.range_ι]; exact hCclosed)
  have hkersupp : ((Scheme.Hom.ker C.ι).support : Set X) = (Z : Set X) := by
    rw [Scheme.Hom.support_ker, C.range_ι, hCclosed.closure_eq]
    exact hZ.symm
  have hZsupp : (Scheme.Hom.ker C.ι).support = Z := TopologicalSpace.Closeds.ext hkersupp
  have hvan : Scheme.IdealSheafData.vanishingIdeal Z = (Scheme.Hom.ker C.ι).radical := by
    rw [← hZsupp]
    exact Scheme.IdealSheafData.vanishingIdeal_support
  have hsupp : (Scheme.IdealSheafData.vanishingIdeal Z).support = Z := by
    rw [hvan, Scheme.IdealSheafData.support_radical]
    exact hZsupp
  have hrange :
      Set.range ⇑(Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = (C : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι, hsupp]
    exact hZ
  have hle : Scheme.Hom.ker C.ι ≤
      Scheme.Hom.ker (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι := by
    rw [Scheme.IdealSheafData.ker_subschemeι, hvan]
    exact Scheme.IdealSheafData.le_radical _
  let φ : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ⟶ C.toScheme :=
    IsClosedImmersion.lift C.ι (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι hle
  have hφ : φ ≫ C.ι = (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι :=
    IsClosedImmersion.lift_fac _ _ hle
  have hφbase : ∀ x, ⇑C.ι (⇑φ x) =
      ⇑(Scheme.IdealSheafData.vanishingIdeal Z).subschemeι x := by
    intro x
    rw [← hφ]
    simp
  have hinj : Function.Injective ⇑C.ι := C.ι.isOpenEmbedding.injective
  have hsurj : Function.Surjective ⇑φ := by
    intro y
    have hy : ⇑C.ι y ∈ Set.range ⇑(Scheme.IdealSheafData.vanishingIdeal Z).subschemeι := by
      rw [hrange, ← C.range_ι]
      exact Set.mem_range_self y
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, hinj ?_⟩
    rw [hφbase x]
    exact hx
  have : IsPreimmersion (φ ≫ C.ι) := by rw [hφ]; infer_instance
  have : IsPreimmersion φ := IsPreimmersion.of_comp φ C.ι
  have : IsClosedImmersion φ :=
    IsClosedImmersion.of_isPreimmersion φ (by rw [hsurj.range_eq]; exact isClosed_univ)
  have hker : Scheme.Hom.ker φ = ⊥ := by
    rw [← Scheme.IdealSheafData.support_eq_top_iff]
    refine TopologicalSpace.Closeds.ext ?_
    rw [Scheme.Hom.support_ker, hsurj.range_eq, closure_univ]
    simp
  have : IsIso φ := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  exact ⟨asIso φ, hφ⟩
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution
    {X : Scheme} [IsReduced X] (C : X.Opens) (hC : IsClosed (C : Set X)) :
    ∃ e : (Scheme.IdealSheafData.vanishingIdeal
        (⟨(C : Set X), hC⟩ : TopologicalSpace.Closeds X)).subscheme ≅ C.toScheme,
      e.hom ≫ C.ι =
        (Scheme.IdealSheafData.vanishingIdeal
          (⟨(C : Set X), hC⟩ : TopologicalSpace.Closeds X)).subschemeι :=
  exists_iso_subscheme_vanishingIdeal_of_coe_eq C _ rfl
end FunctorialResolution.EmbeddedResolution
