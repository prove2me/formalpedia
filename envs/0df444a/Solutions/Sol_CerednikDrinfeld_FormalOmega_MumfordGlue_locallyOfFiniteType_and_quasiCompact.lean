-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.MumfordGlue.locallyOfFiniteType_and_quasiCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/6a0f49e8-ba4e-5ef8-b604-8584e9dbe6aa

import Definitions.Def_CerednikDrinfeld_MumfordGlue
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlue_locallyOfFiniteType_and_quasiCompact

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
    ∀ n : ℕ, LocallyOfFiniteType (Gl.zb n) ∧ QuasiCompact (Gl.zb n) := by
  classical
  intro n

  let I : Ideal (chartERing 𝒪 π r) := Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}
  let J : Ideal 𝒪 := Ideal.span {π ^ (n + 1)}
  have hJI : J ≤ I.comap (algebraMap 𝒪 (chartERing 𝒪 π r)) := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_pow]
    exact Ideal.subset_span rfl
  let φ : 𝒪 ⧸ J →+* chartERing 𝒪 π r ⧸ I := Ideal.quotientMap I (algebraMap 𝒪 (chartERing 𝒪 π r)) hJI
  have hφmk : φ.comp (Ideal.Quotient.mk J) = algebraMap 𝒪 (chartERing 𝒪 π r ⧸ I) :=
    RingHom.ext fun o => by rw [RingHom.comp_apply]; exact Ideal.quotientMap_mk

  have hφft : φ.FiniteType := by
    letI : Algebra (𝒪 ⧸ J) (chartERing 𝒪 π r ⧸ I) := φ.toAlgebra
    haveI : IsScalarTower 𝒪 (𝒪 ⧸ J) (chartERing 𝒪 π r ⧸ I) :=
      IsScalarTower.of_algebraMap_eq (fun o => (congrArg (fun g : 𝒪 →+* _ => g o) hφmk).symm)
    haveI h0 : Algebra.FiniteType 𝒪 (edgeQuot 𝒪 π) :=
      (inferInstance : Algebra.FiniteType 𝒪 (MvPolynomial (Fin 2) 𝒪)).of_surjective (edgeQuot.mk 𝒪 π)
        Ideal.Quotient.mk_surjective
    haveI h1 : Algebra.FiniteType (edgeQuot 𝒪 π) (chartERing 𝒪 π r) := inferInstance
    haveI h2 : Algebra.FiniteType 𝒪 (chartERing 𝒪 π r) := h0.trans h1
    haveI h3 : Algebra.FiniteType 𝒪 (chartERing 𝒪 π r ⧸ I) :=
      h2.of_surjective (Ideal.Quotient.mkₐ 𝒪 I) Ideal.Quotient.mk_surjective
    exact Algebra.FiniteType.of_restrictScalars_finiteType 𝒪 (𝒪 ⧸ J) (chartERing 𝒪 π r ⧸ I)

  have hζ : ∀ h : Matrix.GeneralLinearGroup (Fin 2) K₀, Gl.ζ h n ≫ Gl.zb n = Spec.map (CommRingCat.ofHom φ) := by
    intro h
    haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ J)))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ J)))), Category.assoc, Gl.ζ_over h n,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  obtain ⟨S, hS⟩ := Gl.ζ_cover n
  refine ⟨?_, ?_⟩
  ·
    let 𝒰 : (Gl.Z n).OpenCover := Scheme.Cover.mkOfCovers (S : Set (Matrix.GeneralLinearGroup (Fin 2) K₀))
      (fun _ => Spec (CommRingCat.of (chartERing 𝒪 π r ⧸ I))) (fun h => Gl.ζ h.1 n)
      (fun z => by obtain ⟨h, hh, y, hy⟩ := hS z; exact ⟨⟨h, hh⟩, y, hy⟩) (fun h => Gl.ζ_isOpenImmersion h.1 n)
    refine IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType) 𝒰 (fun h => ?_)
    show LocallyOfFiniteType (Gl.ζ h.1 n ≫ Gl.zb n)
    rw [hζ, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact hφft
  ·
    haveI : CompactSpace (Gl.Z n) := by
      refine ⟨?_⟩
      have : (Set.univ : Set (Gl.Z n)) ⊆ ⋃ h ∈ (S : Set (Matrix.GeneralLinearGroup (Fin 2) K₀)), Set.range (Gl.ζ h n).base := by
        intro z _
        obtain ⟨h, hh, hz⟩ := hS z
        exact Set.mem_biUnion hh hz
      have hc : ∀ h : Matrix.GeneralLinearGroup (Fin 2) K₀, IsCompact (Set.range (Gl.ζ h n).base) := fun h =>
        @isCompact_range _ _ _ _ (PrimeSpectrum.compactSpace : CompactSpace (PrimeSpectrum (chartERing 𝒪 π r ⧸ I))) _
          (Gl.ζ h n).base.hom.continuous
      exact (S.finite_toSet.isCompact_biUnion fun h _ => hc h).of_isClosed_subset isClosed_univ this
    exact (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr ‹_›

end S_CerednikDrinfeld_FormalOmega_MumfordGlue_locallyOfFiniteType_and_quasiCompact
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlue_locallyOfFiniteType_and_quasiCompact (solution)
