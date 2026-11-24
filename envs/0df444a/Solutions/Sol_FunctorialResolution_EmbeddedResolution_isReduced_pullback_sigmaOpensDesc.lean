-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isReduced_pullback_sigmaOpensDesc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:49:10.413457+00:00
-- url     : https://prove2.me/submissions/3533c487-cab9-4e87-9d82-2a4cf951ec86

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DisjointUnionOfOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DisjointUnionOfOpensPullback
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_sigma___sigmaOpensDesc_a310daec50eb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FunctorialResolution.EmbeddedResolution
universe u
private theorem isReduced_of_isOpenImmersion_cover {X : Scheme.{u}} {J : Type u} {V : J → Scheme.{u}}
    (m : (j : J) → V j ⟶ X) (hm : ∀ j, IsOpenImmersion (m j))
    (hV : ∀ j, AlgebraicGeometry.IsReduced (V j))
    (hcov : ∀ x : ↥X, ∃ (j : J) (y : ↥(V j)), (m j).base y = x) :
    AlgebraicGeometry.IsReduced X := by
  have : ∀ x : ↥X, _root_.IsReduced ↥(X.presheaf.stalk x) := by
    intro x
    obtain ⟨j, y, hy⟩ := hcov x
    have := hm j
    have := hV j
    subst hy
    exact isReduced_of_injective (CommRingCat.Hom.hom ((m j).stalkMap y))
      (asIso ((m j).stalkMap y)).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk X
private theorem exists_sigma_ι_base_eq {J : Type u} (f : J → Scheme.{u}) (x : ↥(∐ f)) :
    ∃ (j : J) (y : ↥(f j)), (Sigma.ι f j).base y = x := by
  refine ⟨((sigmaMk f).symm x).1, ((sigmaMk f).symm x).2, ?_⟩
  rw [← sigmaMk_mk]
  simp
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
universe u
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens)
    (W' : Scheme.{u}) [IsReduced W'] (g' : W' ⟶ Y) :
    IsReduced (pullback g' (sigmaOpensDesc Y U)) := by
  refine isReduced_of_isOpenImmersion_cover
    (fun i => pullback.fst (pullback.snd g' (sigmaOpensDesc Y U))
      (Sigma.ι (fun j => (U j).toScheme) i)) (fun i => inferInstance) ?_ ?_
  · intro i
    have hoi : IsOpenImmersion
        (Sigma.ι (fun j => (U j).toScheme) i ≫ sigmaOpensDesc Y U) := by
      rw [sigma_ι_sigmaOpensDesc]
      infer_instance
    have : IsReduced
        (pullback g' (Sigma.ι (fun j => (U j).toScheme) i ≫ sigmaOpensDesc Y U)) :=
      isReduced_of_isOpenImmersion
        (pullback.fst g' (Sigma.ι (fun j => (U j).toScheme) i ≫ sigmaOpensDesc Y U))
    exact isReduced_of_isOpenImmersion
      (pullbackLeftPullbackSndIso g' (sigmaOpensDesc Y U)
        (Sigma.ι (fun j => (U j).toScheme) i)).hom
  · intro x
    obtain ⟨i, y, hy⟩ :=
      exists_sigma_ι_base_eq (fun j => (U j).toScheme)
        ((pullback.snd g' (sigmaOpensDesc Y U)).base x)
    obtain ⟨z, hz1, _⟩ :=
      Scheme.Pullback.exists_preimage_pullback
        (f := pullback.snd g' (sigmaOpensDesc Y U))
        (g := Sigma.ι (fun j => (U j).toScheme) i) x y hy.symm
    exact ⟨i, z, hz1⟩
end FunctorialResolution.EmbeddedResolution
