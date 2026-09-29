-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.MumfordGlueLevel.isPullback_zb_of_forall_zeta_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/4c3cdba8-04fd-5e9e-b2ac-fef991c4d8a2

import Definitions.Def_CerednikDrinfeld_MumfordGlueLevel
import Theorems.Thm_AlgebraicGeometry_isPullback_of_openCover_of_isPullback_morphismRestrict
import Theorems.Thm_CerednikDrinfeld_FormalOmega_isPullback_Spec_map_factor_chartERing
import Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlueLevel_preimage_opensRange_zeta_eq_of_forall_zeta_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlueLevel_isPullback_zb_of_forall_zeta_comp_eq
p2m_attr_erase "instance" "CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem solution
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (N : Subgroup (PGL(2, K₀))) (n : ℕ)
    (L : MumfordGlueLevel 𝒪 π K₀ r g₁ N n) (L' : MumfordGlueLevel 𝒪 π K₀ r g₁ N (n + 1))
    (zt : L.Z ⟶ L'.Z)
    (hzt : ∀ h : Matrix.GeneralLinearGroup (Fin 2) K₀,
      L.ζ h ≫ zt = Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 (chartERing 𝒪 π r) π) (Nat.le_succ (n + 1)))))) ≫ L'.ζ h) :
    IsPullback zt L.zb L'.zb
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))) := by
  classical
  haveI hζo : ∀ h, IsOpenImmersion (L.ζ h) := L.ζ_isOpenImmersion
  haveI hζo' : ∀ h, IsOpenImmersion (L'.ζ h) := L'.ζ_isOpenImmersion

  have hle : ∀ m : ℕ, Ideal.span {π ^ (m + 1)} ≤
      (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (m + 1)}).comap (algebraMap 𝒪 (chartERing 𝒪 π r)) := by
    intro m
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]
    exact Ideal.subset_span rfl
  let q : ∀ m : ℕ, (𝒪 ⧸ Ideal.span {π ^ (m + 1)}) →+* ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (m + 1)})) :=
    fun m => Ideal.quotientMap _ (algebraMap 𝒪 (chartERing 𝒪 π r)) (hle m)
  have hq : ∀ m : ℕ, (q m).comp (Ideal.Quotient.mk (Ideal.span {π ^ (m + 1)})) =
      (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (m + 1)})).comp (algebraMap 𝒪 (chartERing 𝒪 π r)) :=
    fun m => RingHom.ext fun x => rfl

  let fA := Ideal.Quotient.factor
    (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 (chartERing 𝒪 π r) π) (Nat.le_succ (n + 1))))
  let fO := Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))

  have hmk : ∀ m : ℕ, algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (m + 1)}) = Ideal.Quotient.mk _ := fun m => rfl
  have hζzb : ∀ h, L.ζ h ≫ L.zb = Spec.map (CommRingCat.ofHom (q n)) := by
    intro h
    haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))), Category.assoc,
      L.ζ_over h, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hmk, hq]
  have hζzb' : ∀ h, L'.ζ h ≫ L'.zb = Spec.map (CommRingCat.ofHom (q (n + 1))) := by
    intro h
    haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1 + 1)})))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1 + 1)})))), Category.assoc,
      L'.ζ_over h, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hmk, hq]

  have hsq : fA.comp (q (n + 1)) = (q n).comp fO := by
    apply Ideal.Quotient.ringHom_ext
    rw [RingHom.comp_assoc, RingHom.comp_assoc, hq]
    rfl

  have w : zt ≫ L'.zb = L.zb ≫ Spec.map (CommRingCat.ofHom fO) := by
    let 𝒱 : L.Z.OpenCover := Scheme.Cover.mkOfCovers (Matrix.GeneralLinearGroup (Fin 2) K₀)
      (fun _ => Spec (CommRingCat.of ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))))
      (fun h => L.ζ h) (fun z => by obtain ⟨S, hS⟩ := L.ζ_cover; obtain ⟨h, -, y, hy⟩ := hS z; exact ⟨h, y, hy⟩)
    refine Scheme.Cover.hom_ext 𝒱 _ _ fun h => ?_
    show L.ζ h ≫ zt ≫ L'.zb = L.ζ h ≫ L.zb ≫ Spec.map (CommRingCat.ofHom fO)
    rw [← Category.assoc, hzt, Category.assoc, hζzb', ← Category.assoc, hζzb, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun φ => Spec.map (CommRingCat.ofHom φ)) hsq

  let 𝒰 : L'.Z.OpenCover := Scheme.Cover.mkOfCovers (Matrix.GeneralLinearGroup (Fin 2) K₀)
    (fun _ => Spec (CommRingCat.of ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1 + 1)}))))
    (fun h => L'.ζ h) (fun z => by obtain ⟨S, hS⟩ := L'.ζ_cover; obtain ⟨h, -, y, hy⟩ := hS z; exact ⟨h, y, hy⟩)
  apply AlgebraicGeometry.isPullback_of_openCover_of_isPullback_morphismRestrict zt L.zb L'.zb _ w 𝒰
  intro h
  change IsPullback (zt ∣_ (L'.ζ h).opensRange) ((zt ⁻¹ᵁ (L'.ζ h).opensRange).ι ≫ L.zb) ((L'.ζ h).opensRange.ι ≫ L'.zb) _
  have hpre : zt ⁻¹ᵁ (L'.ζ h).opensRange = (L.ζ h).opensRange :=
    MumfordGlueLevel.preimage_opensRange_zeta_eq_of_forall_zeta_comp_eq 𝒪 hdvr π hπ hres K₀ g₁ hg₁ N n L L' zt hzt h
  let e₁ : Spec (CommRingCat.of ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) ≅
      ↑(zt ⁻¹ᵁ (L'.ζ h).opensRange) := (L.ζ h).isoOpensRange ≪≫ L.Z.isoOfEq hpre.symm
  let e₂ : Spec (CommRingCat.of ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1 + 1)}))) ≅
      ↑((L'.ζ h).opensRange) := (L'.ζ h).isoOpensRange
  have he₁ : e₁.hom ≫ (zt ⁻¹ᵁ (L'.ζ h).opensRange).ι = L.ζ h := by
    show ((L.ζ h).isoOpensRange.hom ≫ (L.Z.isoOfEq hpre.symm).hom) ≫ _ = _
    rw [Category.assoc, Scheme.isoOfEq_hom_ι, Scheme.Hom.isoOpensRange_hom_ι]
  have he₂ : e₂.hom ≫ ((L'.ζ h).opensRange).ι = L'.ζ h := Scheme.Hom.isoOpensRange_hom_ι _
  refine IsPullback.of_iso (isPullback_Spec_map_factor_chartERing 𝒪 π r n (q n) (hq n) (q (n + 1)) (hq (n + 1)))
    e₁ e₂ (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [← cancel_mono ((L'.ζ h).opensRange).ι, Category.assoc, Category.assoc, he₂, morphismRestrict_ι,
      ← Category.assoc, he₁, hzt]
  · rw [Iso.refl_hom, Category.comp_id, ← Category.assoc, he₁, hζzb]
  · rw [Iso.refl_hom, Category.comp_id, ← Category.assoc, he₂, hζzb']
  · rw [Iso.refl_hom, Category.comp_id, Iso.refl_hom, Category.id_comp]

end S_CerednikDrinfeld_FormalOmega_MumfordGlueLevel_isPullback_zb_of_forall_zeta_comp_eq
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlueLevel_isPullback_zb_of_forall_zeta_comp_eq (solution)
