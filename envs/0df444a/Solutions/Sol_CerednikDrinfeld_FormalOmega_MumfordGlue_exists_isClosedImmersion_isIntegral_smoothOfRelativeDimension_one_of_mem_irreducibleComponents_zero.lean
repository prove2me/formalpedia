-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.MumfordGlue.exists_isClosedImmersion_isIntegral_smoothOfRelativeDimension_one_of_mem_irreducibleComponents_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/dce4fbac-407a-594f-b763-a60a27f147e5

import Definitions.Def_CerednikDrinfeld_MumfordGlue
import Theorems.Thm_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_smoothOfRelativeDimension_restrict_subscheme_vanishingIdeal_of_isOpenImmersion
import Theorems.Thm_CerednikDrinfeld_FormalOmega_chartERing_smoothOfRelativeDimension_one_specMap_quotient_of_mem_minimalPrimes_level_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlue_exists_isClosedImmersion_isIntegral_smoothOfRelativeDimension_one_of_mem_irreducibleComponents_zero

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem solution
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (N : Subgroup (PGL(2, K₀)))
    (Gl : MumfordGlue 𝒪 π K₀ r g₁ N)
    :
    ∀ Y ∈ irreducibleComponents (Gl.Z 0), ∃ (C : Scheme.{0}) (i : C ⟶ Gl.Z 0),
      IsClosedImmersion i ∧ IsIntegral C ∧ Set.range i.base = Y ∧ SmoothOfRelativeDimension 1 (i ≫ Gl.zb 0) := by
  intro Y hY
  let Yc : TopologicalSpace.Closeds (Gl.Z 0) := ⟨Y, isClosed_of_mem_irreducibleComponents Y hY⟩
  refine ⟨(Scheme.IdealSheafData.vanishingIdeal Yc).subscheme, (Scheme.IdealSheafData.vanishingIdeal Yc).subschemeι,
    inferInstance, ?_, ?_, ?_⟩
  · exact AlgebraicGeometry.Scheme.isIntegral_subscheme_vanishingIdeal Yc hY.1
  · rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  ·
    have hπmax : (Ideal.span ({π} : Set 𝒪)).IsMaximal := by
      haveI := hdvr
      exact PrincipalIdealRing.isMaximal_of_irreducible hπ
    let U : Matrix.GeneralLinearGroup (Fin 2) K₀ → (Scheme.IdealSheafData.vanishingIdeal Yc).subscheme.Opens := fun h =>
      (Scheme.IdealSheafData.vanishingIdeal Yc).subschemeι ⁻¹ᵁ
        (@Scheme.Hom.opensRange _ _ (Gl.ζ h 0) (Gl.ζ_isOpenImmersion h 0))
    have hU : TopologicalSpace.IsOpenCover U := by
      rw [TopologicalSpace.IsOpenCover, eq_top_iff]
      rintro c -
      obtain ⟨S, hS⟩ := Gl.ζ_cover 0
      obtain ⟨h, -, hz⟩ := hS ((Scheme.IdealSheafData.vanishingIdeal Yc).subschemeι.base c)
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨h, hz⟩
    apply IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension 1)
      ((Scheme.IdealSheafData.vanishingIdeal Yc).subscheme.openCoverOfIsOpenCover U hU)
    intro h
    haveI := Gl.ζ_isOpenImmersion h 0
    show SmoothOfRelativeDimension 1 ((U h).ι ≫ (Scheme.IdealSheafData.vanishingIdeal Yc).subschemeι ≫ Gl.zb 0)
    apply AlgebraicGeometry.Scheme.IdealSheafData.smoothOfRelativeDimension_restrict_subscheme_vanishingIdeal_of_isOpenImmersion
      (Gl.zb 0) Yc hY ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) (Gl.ζ h 0) 1
    intro P hPmin _hzero

    have hfac : Gl.ζ h 0 ≫ Gl.zb 0 = Spec.map (CommRingCat.ofHom
        (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (algebraMap 𝒪 (chartERing 𝒪 π r))
        (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr (by rw [map_pow]; exact Ideal.subset_span rfl)))))) := by
      haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})))) := by
        rw [Ideal.Quotient.algebraMap_eq]
        exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
      rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})))), Category.assoc,
        Gl.ζ_over h 0, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
    rw [hfac, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact CerednikDrinfeld.FormalOmega.chartERing.smoothOfRelativeDimension_one_specMap_quotient_of_mem_minimalPrimes_level_zero
      𝒪 π r hπmax P hPmin

end S_CerednikDrinfeld_FormalOmega_MumfordGlue_exists_isClosedImmersion_isIntegral_smoothOfRelativeDimension_one_of_mem_irreducibleComponents_zero
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlue_exists_isClosedImmersion_isIntegral_smoothOfRelativeDimension_one_of_mem_irreducibleComponents_zero (solution)
