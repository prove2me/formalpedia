-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.comap_vanishingIdeal_sUnion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:22:48.06199+00:00
-- url     : https://prove2.me/submissions/0ce28f00-6471-4085-a8e0-6fdb8ebe4e46

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_KernelFlatBaseChange
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_VanishingIdealOfComponents
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_compl_sUnion_irreducibleComponents_sdiff_subset
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_closure_compl_sUnion_irreducibleComponents_sdiff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_vanishingIdeal_congr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coe_complSUnionOtherComponents
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_ker_eq_comap_ker_of_isPullback_of_flat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.coe_complSUnionOtherComponents
section
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FunctorialResolution.EmbeddedResolution
variable {α : Type*} [TopologicalSpace α]
private theorem radical_ringHom_ker_eq {R S : Type*} [CommRing R] [CommRing S] [_root_.IsReduced S]
    (φ : R →+* S) : (RingHom.ker φ).radical = RingHom.ker φ := by
  refine le_antisymm ?_ Ideal.le_radical
  rintro x ⟨n, hn⟩
  rw [RingHom.mem_ker] at hn ⊢
  have hx : φ x ^ n = 0 := by rw [← map_pow]; exact hn
  exact IsNilpotent.eq_zero ⟨n, hx⟩
private theorem radical_scheme_ker_eq {X Y : Scheme.{u}} (g : X ⟶ Y)
    [AlgebraicGeometry.IsReduced X] :
    (Scheme.Hom.ker g).radical = Scheme.Hom.ker g := by
  refine le_antisymm ?_ (Scheme.IdealSheafData.le_radical _)
  show (Scheme.Hom.ker g).radical ≤
    Scheme.IdealSheafData.ofIdeals fun U => RingHom.ker (CommRingCat.Hom.hom (g.app U.1))
  refine Scheme.IdealSheafData.le_ofIdeals_iff.mpr ?_
  intro U
  have := AlgebraicGeometry.IsReduced.component_reduced (X := X) (g ⁻¹ᵁ U.1)
  have hle : (Scheme.Hom.ker g).ideal U ≤ RingHom.ker (CommRingCat.Hom.hom (g.app U.1)) := by
    unfold AlgebraicGeometry.Scheme.Hom.ker
    exact Scheme.IdealSheafData.ideal_ofIdeals_le _ U
  rw [Scheme.IdealSheafData.radical_ideal]
  calc ((Scheme.Hom.ker g).ideal U).radical
      ≤ (RingHom.ker (CommRingCat.Hom.hom (g.app U.1))).radical := Ideal.radical_mono hle
    _ = RingHom.ker (CommRingCat.Hom.hom (g.app U.1)) := radical_ringHom_ker_eq _
private theorem ker_eq_vanishingIdeal_of_support {X Y : Scheme.{u}} (g : X ⟶ Y)
    [AlgebraicGeometry.IsReduced X] {Z : Closeds ↥Y}
    (hZ : ((Scheme.Hom.ker g).support : Set ↥Y) = (Z : Set ↥Y)) :
    Scheme.Hom.ker g = Scheme.IdealSheafData.vanishingIdeal Z := by
  rw [← vanishingIdeal_congr hZ, Scheme.IdealSheafData.vanishingIdeal_support,
    radical_scheme_ker_eq g]
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {α : Type*} [TopologicalSpace α]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X X' : Scheme.{u}} (f : X' ⟶ X)
    [AlgebraicGeometry.IsReduced X] [AlgebraicGeometry.IsReduced X']
    [NoetherianSpace ↥X] [NoetherianSpace ↥X'] [AlgebraicGeometry.Flat f]
    {S : Set (Set ↥X)} (hS : S ⊆ irreducibleComponents ↥X)
    {Z : Closeds ↥X} (hZ : (Z : Set ↥X) = ⋃₀ S)
    {Z' : Closeds ↥X'} (hZ' : (Z' : Set ↥X') = f.base ⁻¹' (⋃₀ S)) :
    (Scheme.IdealSheafData.vanishingIdeal Z).comap f =
      Scheme.IdealSheafData.vanishingIdeal Z' := by
  have hq1 : QuasiCompact (complSUnionOtherComponents X S).ι :=
    ⟨fun _ _ _ => NoetherianSpace.isCompact _⟩
  have hq2 : QuasiCompact (f ⁻¹ᵁ complSUnionOtherComponents X S).ι :=
    ⟨fun _ _ _ => NoetherianSpace.isCompact _⟩
  have hclU : closure ((complSUnionOtherComponents X S : X.Opens) : Set ↥X) = (Z : Set ↥X) := by
    rw [coe_complSUnionOtherComponents, hZ]
    exact closure_compl_sUnion_irreducibleComponents_sdiff hS
  have h1 : (complSUnionOtherComponents X S).ι.ker = Scheme.IdealSheafData.vanishingIdeal Z := by
    apply ker_eq_vanishingIdeal_of_support
    rw [Scheme.Hom.support_ker, ← hclU]
    congr 1
    exact Scheme.Opens.range_ι _
  have hclU' :
      closure ((f ⁻¹ᵁ complSUnionOtherComponents X S : X'.Opens) : Set ↥X') = (Z' : Set ↥X') := by
    have hcl : IsClosed (⇑f.base ⁻¹' (⋃₀ S)) := by
      rw [← hZ']; exact Z'.2
    rw [hZ']
    show closure (⇑f.base ⁻¹' ((⋃₀ (irreducibleComponents ↥X \ S))ᶜ))
        = ⇑f.base ⁻¹' (⋃₀ S)
    apply Set.Subset.antisymm
    · exact closure_minimal
        (Set.preimage_mono (compl_sUnion_irreducibleComponents_sdiff_subset S)) hcl
    · intro x' hx'
      have hx'' : f.base x' ∈ ⋃₀ S := hx'
      obtain ⟨C, hCS, hfx⟩ := hx''
      have hCcomp : C ∈ irreducibleComponents ↥X := hS hCS
      obtain ⟨η, hη⟩ :=
        QuasiSober.sober hCcomp.1 (isClosed_of_mem_irreducibleComponents C hCcomp)
      have hηU : η ∈ (⋃₀ (irreducibleComponents ↥X \ S))ᶜ := by
        rintro ⟨D, ⟨hDcomp, hDS⟩, hηD⟩
        have hCsubD : C ⊆ D := by
          rw [← hη]
          exact (isClosed_of_mem_irreducibleComponents D hDcomp).closure_subset_iff.mpr
            (Set.singleton_subset_iff.mpr hηD)
        have hDsubC : D ⊆ C := hCcomp.2 hDcomp.1 hCsubD
        exact hDS (Set.Subset.antisymm hCsubD hDsubC ▸ hCS)
      have hspec : η ⤳ f.base x' := by
        rw [specializes_iff_mem_closure, hη]
        exact hfx
      obtain ⟨y', hy'spec, hy'eq⟩ := AlgebraicGeometry.Flat.generalizingMap f hspec
      have hy'mem : f.base y' ∈ ((⋃₀ (irreducibleComponents ↥X \ S))ᶜ) := by
        rw [hy'eq]; exact hηU
      have hy'mem2 : y' ∈ (⇑f.base ⁻¹' ((⋃₀ (irreducibleComponents ↥X \ S))ᶜ)) := hy'mem
      exact closure_mono (Set.singleton_subset_iff.mpr hy'mem2)
        (specializes_iff_mem_closure.mp hy'spec)
  have h2 : (f ⁻¹ᵁ complSUnionOtherComponents X S).ι.ker = Scheme.IdealSheafData.vanishingIdeal Z' := by
    apply ker_eq_vanishingIdeal_of_support
    rw [Scheme.Hom.support_ker, ← hclU']
    congr 1
    exact Scheme.Opens.range_ι _
  have hpb := isPullback_morphismRestrict f (complSUnionOtherComponents X S)
  have h4 := ker_eq_comap_ker_of_isPullback_of_flat hpb
  rw [← h1, ← h2, h4]
end FunctorialResolution.EmbeddedResolution
